module

public import Mathlib.Tactic.Group
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Proper.Bijection
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison

/-!
# Injectivity in the functoriality of Galois categories

The homomorphism of automorphism groups associated to a functor between Galois categories is
injective exactly when every connected object of the target is covered by an object that embeds
in the image of an object of the source.

## Main results

* `CategoryTheory.injective_inducedHom_iff_exists_epi_mono_of_fiberIso` characterizes injectivity
  of the continuous homomorphism produced by a choice of fibre-functor isomorphism by such
  epimorphism–monomorphism diagrams.
* `CategoryTheory.injective_inducedHom_iff_exists_epi_mono` is the same equivalence for an
  arbitrary `CategoryTheory.GaloisFunctorData` over that isomorphism.

## Implementation notes

The functoriality square is recorded by `CategoryTheory.GaloisFunctorData`. Nothing in it is
assumed: the continuous homomorphism of the diagram and the 2-isomorphism of the square are
both *constructed* from the fibre-functor isomorphism by
`CategoryTheory.galoisFunctorDataOfFiberIso`. Its action equivalence also allows the statement
without separately assuming exactness of the functor: the corresponding restriction-of-actions
functor is exact. The diagram is expressed using categorical epimorphisms and monomorphisms in
the target Galois category.

## References

* [Stacks Project, Tag 0BN7](https://stacks.math.columbia.edu/tag/0BN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' w

namespace CategoryTheory

universe uG

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

private theorem exists_openSubgroup_comap_le
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [TotallyDisconnectedSpace K]
    (f : G →ₜ* K) (hf : Function.Injective f) (U : OpenSubgroup G) :
    ∃ V : OpenSubgroup K, ∀ g : G, f g ∈ V → g ∈ U := by
  let S : Set K := f '' (U : Set G)ᶜ
  have hS : IsClosed S := ((isCompact_univ.of_isClosed_subset U.isOpen.isClosed_compl
    (by simp)).image f.continuous).isClosed
  have hone : (1 : K) ∉ S := by
    rintro ⟨g, hg, hgf⟩
    obtain rfl : g = 1 := hf (by simpa using hgf)
    exact hg U.one_mem
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hS.isOpen_compl (by simpa using hone)
  refine ⟨V.toOpenSubgroup, fun g hgV => ?_⟩
  by_contra hgU
  exact hV hgV ⟨g, hgU, rfl⟩

private def quotientMapOfComap
    {G K : Type*} [Group G] [Group K] (f : G →* K)
    (V : Subgroup K) (W : Subgroup G) (hW : W ≤ V.comap f) : G ⧸ W → K ⧸ V :=
  Quotient.lift (fun g : G => (Quotient.mk (QuotientGroup.leftRel V) (f g))) (by
    intro a b hab
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using hW (QuotientGroup.leftRel_apply.mp hab))

private theorem quotientMapOfComap_injective
    {G K : Type*} [Group G] [Group K] (f : G →* K)
    (V : Subgroup K) (W : Subgroup G) (hW : W = V.comap f) :
    Function.Injective (quotientMapOfComap f V W hW.le) := by
  intro x y h
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      have hrel : QuotientGroup.leftRel V (f a) (f b) := Quotient.exact h
      have hv : f a⁻¹ * f b ∈ V := by
        simpa only [map_inv] using QuotientGroup.leftRel_apply.mp hrel
      rw [hW]
      simpa using hv

private theorem quotientMapOfComap_smul
    {G K : Type*} [Group G] [Group K] (f : G →* K)
    (V : Subgroup K) (W : Subgroup G) (hW : W ≤ V.comap f)
    (g : G) (x : G ⧸ W) :
    quotientMapOfComap f V W hW (g • x) = f g • quotientMapOfComap f V W hW x := by
  induction x using Quotient.inductionOn' with
  | h x => simp [quotientMapOfComap]

private def quotientMapToAction
    {G X : Type*} [Group G] [MulAction G X]
    (W : Subgroup G) (x : X) (hW : W ≤ MulAction.stabilizer G x) : G ⧸ W → X :=
  Quotient.lift (fun g : G => g • x) (by
    intro a b hab
    have hfix : (a⁻¹ * b) • x = x :=
      MulAction.mem_stabilizer_iff.mp (hW (QuotientGroup.leftRel_apply.mp hab))
    have hfix' : a⁻¹ • (b • x) = x := by simpa only [mul_smul] using hfix
    simpa [mul_smul] using (congrArg (fun y => a • y) hfix').symm)

private theorem quotientMapToAction_smul
    {G X : Type*} [Group G] [MulAction G X]
    (W : Subgroup G) (x : X) (hW : W ≤ MulAction.stabilizer G x)
    (g : G) (y : G ⧸ W) :
    quotientMapToAction W x hW (g • y) = g • quotientMapToAction W x hW y := by
  induction y using Quotient.inductionOn' with
  | h y => simp [quotientMapToAction, mul_smul]

private theorem quotientMapToAction_surjective
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    (W : Subgroup G) (x : X) (hW : W ≤ MulAction.stabilizer G x) :
    Function.Surjective (quotientMapToAction W x hW) := by
  intro y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  exact ⟨⟦g⟧, hg⟩

/-- The induced homomorphism is injective precisely when every connected target object admits
an epimorphic cover that is a subobject of the image of a source object. -/
@[stacks 0BN7, sga "1 V 6.8"]
public theorem injective_inducedHom_iff_exists_epi_mono
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t) :
    Function.Injective d.hom ↔
      ∀ X'' : C', PreGaloisCategory.IsConnected X'' →
        ∃ (X' : C) (Y'' : C') (p : Y'' ⟶ X'') (i : Y'' ⟶ H.obj X'),
          Epi p ∧ Mono i := by
  classical
  constructor
  · intro hinj X'' hX''
    let : PreGaloisCategory C := preGalois_of_isGaloisCategory F
    let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
    let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
    let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
    let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
    let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
    let : PreGaloisCategory.IsConnected X'' := hX''
    let x : F'.obj X'' := Classical.choice (inferInstance : Nonempty (F'.obj X''))
    let U : OpenSubgroup (Aut F') :=
      ⟨MulAction.stabilizer (Aut F') x, stabilizer_isOpen (Aut F') x⟩
    obtain ⟨V, hV⟩ := exists_openSubgroup_comap_le d.hom hinj U
    let W : OpenSubgroup (Aut F') :=
      OpenSubgroup.comap d.hom.toMonoidHom d.hom.continuous V
    have hWstab : (W : Subgroup (Aut F')) ≤ MulAction.stabilizer (Aut F') x := by
      intro g hg
      exact hV g (by simpa [W, OpenSubgroup.mem_comap] using hg)
    let A := PreGaloisCategory.functorToContAction F
    let B := PreGaloisCategory.functorToContAction F'
    let Q : ContAction FintypeCat.{w} (Aut F) := quotientContActionSwitch V
    obtain ⟨X', ⟨eX'⟩⟩ := Functor.EssSurj.mem_essImage A Q
    let Y : ContAction FintypeCat.{w} (Aut F') := quotientContActionSwitch W
    let QW : Action FintypeCat (Aut F') :=
      (ObjectProperty.ι _).obj (quotientContAction W)
    let QV : Action FintypeCat (Aut F) :=
      (ObjectProperty.ι _).obj (quotientContAction V)
    have hYVobj : Y.obj.V.obj = (FintypeCat.uSwitch.obj QW.V).obj := rfl
    have hWcarrier : QW.V.obj = (Aut F' ⧸ (W : Subgroup (Aut F'))) := rfl
    let eW : Y.obj.V ≃ (Aut F' ⧸ (W : Subgroup (Aut F'))) :=
      (Equiv.cast hYVobj).trans (FintypeCat.uSwitchEquiv QW.V) |>.trans (Equiv.cast hWcarrier)
    let eV : Q.obj.V ≃ (Aut F ⧸ (V : Subgroup (Aut F))) :=
      FintypeCat.uSwitchEquiv QV.V
    have hnat (g : Aut F') (y : Y.obj.V) :
        eW (((Y.obj.ρ g).asHom).hom y) = ((QW.ρ g).asHom).hom (eW y) :=
      (FintypeCat.uSwitchEquiv_naturality ((QW.ρ g).asHom) y).symm
    let pHom : Y.obj ⟶ (B.obj X'').obj := {
      hom := FintypeCat.homMk (fun y => quotientMapToAction (W : Subgroup (Aut F')) x hWstab (eW y))
      comm := by
        intro g
        ext y
        change quotientMapToAction (W : Subgroup (Aut F')) x hWstab
            (eW (((Y.obj.ρ g).asHom).hom y)) =
          g • quotientMapToAction (W : Subgroup (Aut F')) x hWstab (eW y)
        rw [hnat]
        exact quotientMapToAction_smul (W : Subgroup (Aut F')) x hWstab g (eW y) }
    let p0 : Y ⟶ B.obj X'' := ObjectProperty.homMk pHom
    let hcomap : (W : Subgroup (Aut F')) ≤ (V : Subgroup (Aut F)).comap d.hom.toMonoidHom := by
      intro g hg
      exact hg
    let qmap := quotientMapOfComap d.hom.toMonoidHom (V : Subgroup (Aut F))
      (W : Subgroup (Aut F')) hcomap
    let R := (ContAction.res FintypeCat d.hom).obj Q
    have hRV : R.obj.V = Q.obj.V := rfl
    let castR : Q.obj.V → R.obj.V := fun z => hRV.symm ▸ z
    let iHom : Y.obj ⟶ R.obj := {
      hom := FintypeCat.homMk (fun y => castR (eV.symm (qmap (eW y))))
      comm := by
        intro g
        ext y
        change castR (eV.symm (qmap (eW (((Y.obj.ρ g).asHom).hom y)))) =
          ((R.obj.ρ g).asHom).hom (castR (eV.symm (qmap (eW y))))
        have htarget : (R.obj.ρ g).asHom =
            FintypeCat.uSwitch.map ((QV.ρ (d.hom g)).asHom) := rfl
        rw [hnat]
        change castR (eV.symm (qmap (g • eW y))) =
          ((R.obj.ρ g).asHom).hom (castR (eV.symm (qmap (eW y))))
        have hq : qmap (g • eW y) = d.hom g • qmap (eW y) := by
          exact quotientMapOfComap_smul d.hom.toMonoidHom (V : Subgroup (Aut F))
            (W : Subgroup (Aut F')) hcomap g (eW y)
        rw [hq]
        rw [htarget]
        change eV.symm (ConcreteCategory.hom ((QV.ρ (d.hom g)).asHom) (qmap (eW y))) =
          ConcreteCategory.hom (FintypeCat.uSwitch.map ((QV.ρ (d.hom g)).asHom))
            (eV.symm (qmap (eW y)))
        convert (FintypeCat.uSwitchEquiv_symm_naturality
          ((QV.ρ (d.hom g)).asHom) (qmap (eW y))).symm using 1
        · simp [eV, QV, quotientContAction, Action.FintypeCat.ofMulAction]
          rfl }
    let i0 : Y ⟶ (ContAction.res FintypeCat d.hom).obj Q := ObjectProperty.homMk iHom
    let eR : (ContAction.res FintypeCat d.hom).obj Q ≅ B.obj (H.obj X') :=
      (ContAction.res FintypeCat d.hom).mapIso eX'.symm ≪≫ d.actionIso.app X'
    let i1 : Y ⟶ B.obj (H.obj X') := i0 ≫ eR.hom
    obtain ⟨Y'', ⟨eY⟩⟩ := Functor.EssSurj.mem_essImage B Y
    let pMap : B.obj Y'' ⟶ B.obj X'' := eY.hom ≫ p0
    let iMap : B.obj Y'' ⟶ B.obj (H.obj X') := eY.hom ≫ i1
    obtain ⟨p, hp⟩ := B.map_surjective pMap
    obtain ⟨i, hi⟩ := B.map_surjective iMap
    have hp0surj : Function.Surjective (ConcreteCategory.hom p0.hom.hom) := by
      change Function.Surjective (fun y => quotientMapToAction
        (W : Subgroup (Aut F')) x hWstab (eW y))
      intro z
      obtain ⟨q, hq⟩ := quotientMapToAction_surjective
        (W : Subgroup (Aut F')) x hWstab z
      refine ⟨eW.symm q, ?_⟩
      change quotientMapToAction (W : Subgroup (Aut F')) x hWstab (eW (eW.symm q)) = z
      rw [eW.apply_symm_apply]
      exact hq
    have heYsurj : Function.Surjective (ConcreteCategory.hom (eY.hom.hom).hom) := by
      let forgetY := CategoryTheory.forget₂ (ContAction FintypeCat (Aut F')) FintypeCat
      have hIso : IsIso (forgetY.map eY.hom) := by infer_instance
      change Function.Surjective (ConcreteCategory.hom (forgetY.map eY.hom))
      exact ((ConcreteCategory.isIso_iff_bijective _).mp hIso).2
    have hpFiber : Function.Surjective
        ((setValuedFiberFunctor F').map p) := by
      change Function.Surjective (ConcreteCategory.hom ((B.map p).hom).hom)
      rw [hp]
      change Function.Surjective
        ((ConcreteCategory.hom p0.hom.hom) ∘ (ConcreteCategory.hom (eY.hom.hom).hom))
      exact Function.Surjective.comp hp0surj heYsurj
    have hiMono : Mono i := by
      have hW_eq : (W : Subgroup (Aut F')) =
          (V : Subgroup (Aut F)).comap d.hom.toMonoidHom := rfl
      have hqinj := quotientMapOfComap_injective d.hom.toMonoidHom
        (V : Subgroup (Aut F)) (W : Subgroup (Aut F')) hW_eq
      have hcastRinj : Function.Injective castR := by
        intro a b hab
        simpa [castR] using hab
      have hiHomFun : Function.Injective (ConcreteCategory.hom iHom.hom) := by
        change Function.Injective (fun y => castR (eV.symm (qmap (eW y))))
        exact hcastRinj.comp (eV.symm.injective.comp (hqinj.comp eW.injective))
      have hiHom : Mono iHom := ConcreteCategory.mono_of_injective iHom hiHomFun
      have hi0 : Mono i0 := by
        apply (ObjectProperty.ι _).mono_of_mono_map
        change Mono iHom
        exact hiHom
      let : Mono i0 := hi0
      have hi1 : Mono i1 := by
        dsimp [i1]
        infer_instance
      let : Mono i1 := hi1
      let : IsIso eY.hom := inferInstance
      have hiMap : Mono iMap := by
        dsimp [iMap]
        infer_instance
      have hiB : Mono (B.map i) := by
        rw [hi]
        exact hiMap
      exact B.mono_of_mono_map hiB
    have hpEpi : Epi p := (epi_iff_surjective_on_fiber
      (setValuedFiberFunctor F') p).2 hpFiber
    exact ⟨X', Y'', p, i, hpEpi, hiMono⟩
  · intro h
    let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
    let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
    let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
    let A := PreGaloisCategory.functorToContAction F
    let B := PreGaloisCategory.functorToContAction F'
    have hmap_natural (g : Aut F') {X Y : C'} (f : X ⟶ Y)
        (x : (B.obj X).obj.V) :
        ConcreteCategory.hom (B.map f).hom.hom
            (ConcreteCategory.hom (((B.obj X).obj.ρ g).asHom) x) =
          ConcreteCategory.hom (((B.obj Y).obj.ρ g).asHom)
            (ConcreteCategory.hom (B.map f).hom.hom x) := by
      have hc := (B.map f).hom.comm g
      have hx := congrArg
        (fun m : (B.obj X).obj.V ⟶ (B.obj Y).obj.V => ConcreteCategory.hom m x) hc
      simpa only [FintypeCat.comp_apply] using hx
    have hfix_map (g : Aut F') {X Y : C'} (f : Y ⟶ X)
        (hY : ∀ y : (B.obj Y).obj.V, ConcreteCategory.hom (((B.obj Y).obj.ρ g).asHom) y = y)
        (x : (B.obj X).obj.V) (y : (B.obj Y).obj.V)
        (hy : ConcreteCategory.hom (B.map f).hom.hom y = x) :
        ConcreteCategory.hom (((B.obj X).obj.ρ g).asHom) x = x := by
      rw [← hy, ← hmap_natural g f y, hY]
    have hfixImage (g : Aut F') (hg : d.hom g = 1) (X : C) :
        ∀ x : (B.obj (H.obj X)).obj.V,
          ConcreteCategory.hom (((B.obj (H.obj X)).obj.ρ g).asHom) x = x := by
      let S := (ContAction.res FintypeCat d.hom).obj (A.obj X)
      let T := B.obj (H.obj X)
      let α := d.actionIso.hom.app X
      have hcomm : (S.obj.ρ g).asHom ≫ α.hom.hom = α.hom.hom ≫ (T.obj.ρ g).asHom :=
        α.hom.comm g
      have hsource : (S.obj.ρ g).asHom = 𝟙 S.obj.V := by
        change ((A.obj X).obj.ρ (d.hom g)).asHom = 𝟙 _
        rw [hg]
        simp
      have : IsIso α := inferInstance
      have : IsIso α.hom := inferInstance
      have : IsIso α.hom.hom := by
        let forgetAction :=
          (forget₂ (Action FintypeCat (Aut F')) FintypeCat)
        have hα : IsIso (forgetAction.map α.hom) := Functor.map_isIso forgetAction α.hom
        change IsIso α.hom.hom at hα
        exact hα
      have htarget : (T.obj.ρ g).asHom = 𝟙 T.obj.V := by
        apply (cancel_epi α.hom.hom).1
        calc
          α.hom.hom ≫ (T.obj.ρ g).asHom = (S.obj.ρ g).asHom ≫ α.hom.hom := hcomm.symm
          _ = α.hom.hom := by rw [hsource]; simp
          _ = α.hom.hom ≫ 𝟙 T.obj.V := (Category.comp_id _).symm
      intro x
      change ConcreteCategory.hom ((T.obj.ρ g).asHom) x = x
      rw [htarget]
      rfl
    have hfixConnected (g : Aut F') (hg : d.hom g = 1) (X : C')
        (hX : PreGaloisCategory.IsConnected X) :
        ∀ x : (B.obj X).obj.V,
          ConcreteCategory.hom (((B.obj X).obj.ρ g).asHom) x = x := by
      obtain ⟨X', Y, p, i, hp, hi⟩ := h X hX
      have hpFiber := (epi_iff_surjective_on_fiber
        (setValuedFiberFunctor F') p).1 hp
      have hiFiber := (IsGaloisCategory.mono_iff_injective
        (setValuedFiberFunctor F') i).1 hi
      have hpB : Function.Surjective (ConcreteCategory.hom (B.map p).hom.hom) := by
        change Function.Surjective (ConcreteCategory.hom (F'.map p))
        exact hpFiber
      have hiB : Function.Injective (ConcreteCategory.hom (B.map i).hom.hom) := by
        change Function.Injective (ConcreteCategory.hom (F'.map i))
        exact hiFiber
      have hfixY : ∀ y : (B.obj Y).obj.V,
          ConcreteCategory.hom (((B.obj Y).obj.ρ g).asHom) y = y := by
        intro y
        apply hiB
        calc
          ConcreteCategory.hom (B.map i).hom.hom
              (ConcreteCategory.hom (((B.obj Y).obj.ρ g).asHom) y) =
              ConcreteCategory.hom (((B.obj (H.obj X')).obj.ρ g).asHom)
                (ConcreteCategory.hom (B.map i).hom.hom y) := hmap_natural g i y
          _ = (B.map i).hom.hom y := hfixImage g hg X' _
      intro x
      obtain ⟨y, hy⟩ := hpB x
      exact hfix_map g p hfixY x y hy
    have hfixAll (g : Aut F') (hg : d.hom g = 1) (X : C') :
        ∀ x : (B.obj X).obj.V,
          ConcreteCategory.hom (((B.obj X).obj.ρ g).asHom) x = x := by
      let G := setValuedFiberFunctor F'
      obtain ⟨ι, A₀, f, hc, _, hconn⟩ :=
        IsGaloisCategory.exists_finite_coproduct_connected
          (F := G) X
      let c : Cofan (fun j => G.obj (A₀ j)) :=
        Cofan.mk (G.obj X) (fun j => G.map (f j))
      have hcG : IsColimit c := isColimitCofanMkObjOfIsColimit G A₀ f hc
      intro x
      obtain ⟨j, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hcG x
      have hmap : ConcreteCategory.hom (B.map (f j)).hom.hom y = x := by
        change (G.map (f j)) y = x
        exact hy
      exact hfix_map g (f j) (hfixConnected g hg (A₀ j) (hconn j)) x y hmap
    intro g₁ g₂ h12
    have hker (g : Aut F') (hg : d.hom g = 1) : g = 1 := by
      ext X x
      exact hfixAll g hg X x
    have hg : d.hom (g₁ * g₂⁻¹) = 1 := by
      simp [map_mul, map_inv, h12]
    have hEq : g₁ * g₂⁻¹ = 1 := hker _ hg
    calc
      g₁ = (g₁ * g₂⁻¹) * g₂ := by group
      _ = 1 * g₂ := by rw [hEq]
      _ = g₂ := one_mul _

/-- The induced homomorphism is injective precisely when every connected target object admits
an epimorphic cover that is a subobject of the image of a source object.

This is the form of the statement in which no part of the functoriality data is assumed: the
continuous homomorphism of the diagram is the one produced from the fibre-functor isomorphism
`t`, whose continuity and whose 2-isomorphism of the functoriality square are constructed. -/
@[stacks 0BN7, sga "1 V 6.8"]
public theorem injective_inducedHom_iff_exists_epi_mono_of_fiberIso
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    Function.Injective (galoisFunctorDataOfFiberIso F F' H t).hom ↔
      ∀ X'' : C', PreGaloisCategory.IsConnected X'' →
        ∃ (X' : C) (Y'' : C') (p : Y'' ⟶ X'') (i : Y'' ⟶ H.obj X'),
          Epi p ∧ Mono i :=
  injective_inducedHom_iff_exists_epi_mono F F' H t (galoisFunctorDataOfFiberIso F F' H t)

end CategoryTheory
