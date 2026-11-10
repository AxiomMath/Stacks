module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocalImage
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# Checking exactness of abelian sheaves on a covering image

A complex of abelian sheaves on a category fibred in groupoids over the big fppf site is exact
as soon as its inverse image along a `1`-morphism of fibred categories is exact, provided the
image of that `1`-morphism covers every object of the target site locally.

## Main results

* `Stacks.exact_of_exact_inverseImage_of_covering_image` detects exactness of a complex of
  abelian sheaves on any of the five sites associated to a category fibred in groupoids over
  the big fppf site.

## Implementation notes

A covering family is represented by the covering sieve it generates. Since a `1`-morphism of
fibred categories lifts pullbacks, its image covers locally exactly when every object in some
covering sieve is isomorphic to an object in its image. The inverse image of abelian sheaves
along such a `1`-morphism is restriction, which is
`CategoryTheory.Functor.sheafPushforwardContinuous` for the inherited topologies, continuity
and cocontinuity being supplied by
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_and_isCocontinuous_inheritedTopology`.

The proof shows that restriction along the `1`-morphism is faithful and reflects exactness. The
auxiliary constructions build, for a map of abelian presheaves, the subpresheaf of sections that
locally lie in its image, and descend a section of the sheafified image to a section of the
target; this is what identifies the image sheaf and makes the reflection argument work.

## References

* [Stacks Project, Tag 06XD](https://stacks.math.columbia.edu/tag/06XD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LocalImage

namespace Stacks

universe u vₓ vᵤ wₓ wᵤ a

/-- Exactness of a complex of abelian sheaves can be checked after pullback to
a fibred category whose image covers the target locally. -/
@[stacks 06XD]
public theorem exact_of_exact_inverseImage_of_covering_image
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰]
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
    (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (F : 𝒰 ⥤ 𝒳)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F)
    (τ : AlgebraicGeometry.SiteKind)
    (hcover : ∀ x : 𝒳, ∃ R : Sieve x,
      R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g →
          ∃ z : 𝒰, Nonempty (y ≅ F.obj z))
    (C : ShortComplex (CategoryTheory.Sheaf
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) Ab.{a})) :
    (letI : p.IsFibered := hp.isFibered
     letI : q.IsFibered := hq.isFibered
     letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
       ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).1
     letI : (F.sheafPushforwardContinuous Ab.{a}
       (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS p τ)
       (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)).PreservesZeroMorphisms :=
       ⟨by intros; rfl⟩
     (C.map (F.sheafPushforwardContinuous Ab.{a}
       (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS p τ)
       (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ))).Exact) → C.Exact := by
  intro hC
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).1
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).2
  let T := F.sheafPushforwardContinuous Ab.{a}
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS p τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  let : PreservesFiniteLimits T :=
    hF.preservesFiniteLimits_inverseImage
      ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS)) Ab.{a}
  have hfaith : T.Faithful := by
    constructor
    intro A D α β hαβ
    apply Sheaf.hom_ext
    ext x s
    obtain ⟨R, hR, hRimage⟩ := hcover x.unop
    have hsep : Presheaf.IsSeparated
        (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) D.obj := D.2.isSeparated
    apply hsep x.unop R hR
    intro y g hg
    obtain ⟨z, ⟨e⟩⟩ := hRimage g hg
    have hpoint := congrArg (fun k : T.obj A ⟶ T.obj D => k.hom.app (op z)) hαβ
    have hval : α.hom.app (op (F.obj z)) (A.obj.map e.inv.op (A.obj.map g.op s)) =
        β.hom.app (op (F.obj z)) (A.obj.map e.inv.op (A.obj.map g.op s)) :=
      congrArg (fun φ => φ (A.obj.map e.inv.op (A.obj.map g.op s))) hpoint
    have hinj : Function.Injective (D.obj.map e.inv.op) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    have hαnat := ConcreteCategory.congr_hom (α.hom.naturality e.inv.op) (A.obj.map g.op s)
    have hβnat := ConcreteCategory.congr_hom (β.hom.naturality e.inv.op) (A.obj.map g.op s)
    have hlocal : α.hom.app (op y) (A.obj.map g.op s) = β.hom.app (op y) (A.obj.map g.op s) :=
      hinj (hαnat.symm.trans (hval.trans hβnat))
    exact (ConcreteCategory.congr_hom (α.hom.naturality g.op) s).symm.trans
      (hlocal.trans (ConcreteCategory.congr_hom (β.hom.naturality g.op) s))
  let : T.Faithful := hfaith
  let : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let hd := hC.condition.choose
  have hd_epi : Epi hd.left.f' := hC.epi_f' hd.left
  let K := kernel C.g
  let i := kernel.ι C.g
  let hK := kernelIsKernel C.g
  let hKT := isLimitOfPreserves T hK
  let ePair : parallelPair C.g (0 : C.X₂ ⟶ C.X₃) ⋙ T ≅
      parallelPair (T.map C.g) (0 : T.obj C.X₂ ⟶ T.obj C.X₃) :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let cTarget : KernelFork (T.map C.g) := KernelFork.ofι (T.map i)
    (show T.map i ≫ T.map C.g = 0 by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
  let eCone :
      (Cone.postcompose ePair.hom).obj
          (T.mapCone (KernelFork.ofι i (kernel.condition C.g))) ≅
        cTarget :=
    Cone.ext (Iso.refl _) (by intro j; cases j <;> simp [ePair, cTarget, Functor.mapCone_π_app])
  have hKT' : IsLimit cTarget :=
    IsLimit.equivOfNatIsoOfIso ePair _ cTarget eCone hKT
  let eK := hKT'.conePointUniqueUpToIso hd.left.hi
  have hmapf : T.map (kernel.lift C.g C.f C.zero) ≫ eK.hom = hd.left.f' := by
    apply (cancel_mono hd.left.i).1
    have hecomp : eK.hom ≫ hd.left.i = T.map i := by
      simpa [eK, cTarget] using
        (IsLimit.conePointUniqueUpToIso_hom_comp hKT' hd.left.hi WalkingParallelPair.zero)
    rw [Category.assoc, hecomp, ← Functor.map_comp, kernel.lift_ι, hd.left.f'_i,
      ShortComplex.map_f]
  have hker_epi : Epi (kernel.lift C.g C.f C.zero) := T.epi_of_epi_map <| by
    rw [(Iso.eq_comp_inv eK).2 hmapf]
    infer_instance
  let J := AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ
  let Z0 : Sheaf J Ab := Sheaf.terminal J (isZero_zero Ab).isTerminal
  have hZ0 : IsZero Z0 := (IsZero.iff_id_eq_zero _).2
    ((Sheaf.isTerminalTerminal J (isZero_zero Ab).isTerminal).hom_ext _ _)
  let hleft : C.LeftHomologyData := {
    K := K
    H := Z0
    i := i
    π := 0
    wi := kernel.condition C.g
    hi := hK
    wπ := by simp
    hπ := CokernelCofork.IsColimit.ofEpiOfIsZero
      (CokernelCofork.ofπ (0 : K ⟶ Z0) (by simp)) hker_epi hZ0
  }
  let G := Subfunctor.range (Functor.whiskerRight C.g.hom (forget Ab))
  have hType : ∀ A : Sheaf J Ab.{a}, Presieve.IsSheaf J (A.obj ⋙ forget Ab) := fun A =>
    (isSheaf_iff_isSheaf_of_type J _).mp (GrothendieckTopology.HasSheafCompose.isSheaf A.obj A.2)
  have hX₃Type := hType C.X₃
  have hmem : ∀ (U : 𝒳ᵒᵖ) (x : C.X₂.obj.obj U),
      G.sieveOfSection (C.g.hom.app U x) ∈ J U.unop := by
    intro U x
    change Presheaf.imageSieve (Functor.whiskerRight C.g.hom (forget Ab))
      ((Functor.whiskerRight C.g.hom (forget Ab)).app U x) ∈ J U.unop
    rw [Presheaf.imageSieve_app (Functor.whiskerRight C.g.hom (forget Ab)) x]
    exact J.top_mem _
  let Qpre := localImagePresheaf J C.g.hom
  have hQunder : Presheaf.IsSheaf J (Qpre ⋙ forget Ab) := by
    change Presheaf.IsSheaf J ((G.sheafify J).toFunctor)
    exact (isSheaf_iff_isSheaf_of_type J _).mpr (G.sheafify_isSheaf hX₃Type)
  let Q : Sheaf J Ab := ⟨Qpre,
    Presheaf.isSheaf_of_isSheaf_comp J Qpre (forget Ab) hQunder⟩
  let p0 : C.X₂.obj ⟶ Qpre := {
    app := fun U => AddCommGrpCat.ofHom {
      toFun := fun x => ⟨(C.g.hom.app U) x, hmem U x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
    naturality := by
      intro U V i
      ext x
      apply Subtype.ext
      change (ConcreteCategory.hom (C.g.hom.app V))
          ((ConcreteCategory.hom (C.X₂.obj.map i)) x) =
        (ConcreteCategory.hom (C.X₃.obj.map i))
          ((ConcreteCategory.hom (C.g.hom.app U)) x)
      exact ConcreteCategory.congr_hom (C.g.hom.naturality i) x }
  let p : C.X₂ ⟶ Q := Sheaf.homEquiv.symm p0
  let j0 : Qpre ⟶ C.X₃.obj := {
    app := fun U => AddCommGrpCat.ofHom {
      toFun := fun x => x.1
      map_zero' := rfl
      map_add' := by intro x y; rfl }
    naturality := by intro U V i; ext x; rfl }
  let j : Q ⟶ C.X₃ := Sheaf.homEquiv.symm j0
  have hpj : p ≫ j = C.g := by
    apply Sheaf.hom_ext
    ext U x
    rfl
  have hj : Mono j := by
    constructor
    intro A α β hab
    apply Sheaf.hom_ext
    ext U x
    have hval := ConcreteCategory.congr_hom (congrArg (fun k : A ⟶ C.X₃ => k.hom.app U) hab) x
    change (j.hom.app U) ((α.hom.app U) x) =
      (j.hom.app U) ((β.hom.app U) x) at hval
    exact Subtype.ext hval
  have hpLoc : Sheaf.IsLocallySurjective p := by
    change Presheaf.IsLocallySurjective J p.hom
    refine ⟨?_⟩
    intro U s
    apply J.superset_covering ?_ s.2
    intro V i hi
    obtain ⟨x, hx⟩ : ∃ x, (Functor.whiskerRight C.g.hom (forget Ab)).app (op V) x =
        (C.X₃.obj ⋙ forget Ab).map i.op s.1 := by
      simpa [G, Subfunctor.range_obj] using hi
    change ∃ x, (p.hom.app (op V)) x = Qpre.map i.op s
    refine ⟨x, Subtype.ext ?_⟩
    change (ConcreteCategory.hom (C.g.hom.app (op V))) x =
      (ConcreteCategory.hom (C.X₃.obj.map i.op)) s.1
    exact hx
  let : Epi p := Sheaf.epi_of_isLocallySurjective p
  have hfp : C.f ≫ p = 0 :=
    (cancel_mono j).1 (by rw [Category.assoc, hpj, C.zero, zero_comp])
  let hcoker : CokernelCofork C.f := CokernelCofork.ofπ p hfp
  have hcokerColim : IsColimit hcoker :=
    CokernelCofork.IsColimit.ofπ' p hfp (by
      intro A k hk
      have hkill : kernel.ι C.g ≫ k = 0 := hker_epi.left_cancellation _ _ (by simp [hk])
      have hAtype := hType A
      let d0 := localImageDesc C hker_epi k hk hAtype
      let d : Q ⟶ A := Sheaf.homEquiv.symm d0
      refine ⟨d, ?_⟩
      apply Sheaf.hom_ext
      ext U x
      let gx := (ConcreteCategory.hom (C.g.hom.app U)) x
      have hgx : gx ∈ G.obj U := ⟨x, rfl⟩
      have hlocal : G.sieveOfSection gx ∈ J U.unop := hmem U x
      have hdesc := sheafifyLift_app_of_mem G
        (localImageRawDesc C hker_epi k hk) hAtype U gx hgx
      change (ConcreteCategory.hom (d0.app U))
          ((ConcreteCategory.hom (p0.app U)) x) =
        (ConcreteCategory.hom (k.hom.app U)) x
      have hp0x : (p0.app U) x = (⟨gx, hlocal⟩ : Qpre.obj U) := Subtype.ext rfl
      have hdesc' : (ConcreteCategory.hom (d0.app U))
          (⟨gx, hlocal⟩ : Qpre.obj U) =
          (ConcreteCategory.hom ((localImageRawDesc C hker_epi k hk).app U))
            ⟨gx, hgx⟩ := by
        dsimp [d0, localImageDesc]
        exact hdesc
      rw [hp0x, hdesc']
      let y := Classical.choose (rawRangePreimage C.g.hom U ⟨gx, hgx⟩)
      have hy : (ConcreteCategory.hom (C.g.hom.app U)) y = gx :=
        Classical.choose_spec (rawRangePreimage C.g.hom U ⟨gx, hgx⟩)
      have hmap := map_sections_eq_of_map_g_eq C.g k hkill U (x := y) (y := x)
        (by simpa [gx] using hy)
      dsimp [localImageRawDesc, y]
      exact hmap
    )
  let gq : Q ⟶ C.X₃ := hcokerColim.desc (CokernelCofork.ofπ C.g C.zero)
  have hgq : gq = j := by
    rw [← cancel_epi p, hpj]
    exact hcokerColim.fac (CokernelCofork.ofπ C.g C.zero) WalkingParallelPair.one
  have hmonoGq : Mono gq := hgq ▸ hj
  let hright : C.RightHomologyData := {
    Q := Q
    H := Z0
    p := p
    ι := 0
    wp := hfp
    hp := hcokerColim
    wι := zero_comp
    hι := by
      have hcond : (0 : Z0 ⟶ Q) ≫ gq = 0 := by simp [gq]
      have hlim := KernelFork.IsLimit.ofMonoOfIsZero
        (KernelFork.ofι (0 : Z0 ⟶ Q) hcond) hmonoGq hZ0
      simpa [gq, CategoryTheory.ShortComplex.RightHomologyData.g'] using hlim
  }
  let hdata : C.HomologyData := {
    left := hleft
    right := hright
    iso := Iso.refl Z0
    comm := by
      apply (cancel_mono j).1
      calc
        (hleft.π ≫ (Iso.refl Z0).hom ≫ hright.ι) ≫ j = 0 := by simp [hright]
        _ = (hleft.i ≫ hright.p) ≫ j := by
          symm
          calc
            (hleft.i ≫ hright.p) ≫ j = hleft.i ≫ (hright.p ≫ j) := by
              simp [Category.assoc]
            _ = hleft.i ≫ C.g := by rw [hpj]
            _ = 0 := hleft.wi
  }
  exact ⟨hdata, hZ0⟩

end Stacks

end
