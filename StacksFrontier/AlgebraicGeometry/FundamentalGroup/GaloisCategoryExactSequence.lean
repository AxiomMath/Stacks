module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Separation.Hausdorff
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Surjectivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.TrivialComposite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exact sequences arising from Galois categories

For two composable exact functors of Galois categories, the corresponding sequence of
automorphism groups is exact precisely when objects on which the first group acts trivially are
the objects coming from the first category.  We also give the equivalent epimorphic-cover
criterion.

## Main definitions

* `Stacks.FundamentalGroup.IsExactSequence` is the topological exactness condition for two
  continuous group homomorphisms.

## Main results

* `Stacks.FundamentalGroup.galoisExact_iff_categorical_conditions` gives the three equivalent
  group-theoretic and categorical conditions.
* `Stacks.FundamentalGroup.galoisExact_iff_categorical_conditions_of_fiberIso` is the same
  equivalence for the continuous homomorphisms produced by the two chosen fibre-functor
  isomorphisms, with no functoriality data assumed.

## Implementation notes

The finite-coproduct condition is `CategoryTheory.IsFiniteCoproductOfTerminal`. In the
group-theoretic condition, the smallest closed normal subgroup containing the image is represented
by the topological closure of the normal closure of that image. The second and third entries of
the `List.TFAE` are respectively parts (2) and (3) of the source.

## References

* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' u'' v'' w uG

namespace Stacks.FundamentalGroup

/-- A morphism from a connected object into the target of a monomorphism factors through the
monomorphism once the fibre of their pullback is nonempty. -/
private theorem exists_comp_eq_of_nonempty_pullback
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] {X Y A : C} (i : X ⟶ Y) [Mono i] (f : A ⟶ Y)
    (hA : PreGaloisCategory.IsConnected A)
    (hne : Nonempty ((setValuedFiberFunctor F).obj (pullback i f))) :
    ∃ q : A ⟶ X, q ≫ i = f := by
  have : IsIso (pullback.snd i f) := by
    refine hA.noTrivialComponent (pullback i f) (pullback.snd i f) fun h0 => ?_
    exact ((Types.initial_iff_empty _).mp
      ⟨h0.isInitialObj (setValuedFiberFunctor F) _⟩).false hne.some
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- In a category satisfying the Galois category axioms, every monomorphism is the inclusion of a
direct summand. -/
private theorem exists_isColimit_binaryCofan_of_mono
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] {X Y : C} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  classical
  let G := setValuedFiberFunctor F
  obtain ⟨ι, A, f, hc, hfin, hconn⟩ :=
    IsGaloisCategory.exists_finite_coproduct_connected (F := G) Y
  let J : Set ι := {j | Nonempty (G.obj (pullback i (f j)))}
  let B : {j // j ∉ J} → C := fun j => A j.1
  let Z := ∐ B
  let u : Z ⟶ Y := Sigma.desc (fun j => f j.1)
  let c : Cofan (fun j => G.obj (A j)) := Cofan.mk (G.obj Y) (fun j => G.map (f j))
  have hcG : IsColimit c := isColimitCofanMkObjOfIsColimit G A f hc
  have hcZ : IsColimit (Cofan.mk (G.obj Z)
      (fun j => G.map (Sigma.ι B j)) : Cofan fun j => G.obj (B j)) :=
    isColimitOfHasCoproductOfPreservesColimit G B
  have hzu (j : {j // j ∉ J}) (a : G.obj (A j.1)) :
      G.map u (G.map (Sigma.ι B j) a) = G.map (f j.1) a := by
    rw [← G.map_comp_apply, Sigma.ι_comp_desc]
  have hrange : Set.range (G.map u) = (Set.range (G.map i))ᶜ := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨j, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hcZ z
      rintro ⟨x, hx⟩
      exact j.2 ⟨(PullbackCone.IsLimit.equivPullbackObj
        (isLimitOfHasPullbackOfPreservesLimit G i (f j.1))).symm ⟨⟨x, a⟩, hx.trans (hzu j a)⟩⟩
    · intro hy
      obtain ⟨j, a, hj⟩ := Cofan.inj_jointly_surjective_of_isColimit hcG y
      have hjnot : j ∉ J := fun hjmem => by
        obtain ⟨q, hq⟩ := exists_comp_eq_of_nonempty_pullback F i (f j) (hconn j) hjmem
        refine hy ⟨G.map q a, ?_⟩
        rw [← G.map_comp_apply, hq]
        exact hj
      exact ⟨_, (hzu ⟨j, hjnot⟩ a).trans hj⟩
  have huinj : Function.Injective (G.map u) := by
    intro z z' hz
    obtain ⟨j, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hcZ z
    obtain ⟨k, b, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hcZ z'
    have heq : c.inj j.1 a = c.inj k.1 b := by
      change G.map u (G.map (Sigma.ι B j) a) = G.map u (G.map (Sigma.ι B k) b) at hz
      rwa [hzu j a, hzu k b] at hz
    obtain rfl : j = k := Subtype.ext (Cofan.eq_of_inj_apply_eq_of_isColimit hcG a b heq)
    obtain rfl := Cofan.inj_injective_of_isColimit hcG j.1 heq
    rfl
  have : Mono (G.map i) := Functor.map_mono G i
  have hc' : Nonempty (IsColimit (BinaryCofan.mk (G.map i) (G.map u))) :=
    (Types.binaryCofan_isColimit_iff _).mpr
      ⟨injective_of_mono (G.map i), huinj, ((eq_compl_iff_isCompl).mp hrange).symm⟩
  exact ⟨Z, u, ⟨isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G i u).symm hc'.some)⟩⟩

/-- The axioms of `IsGaloisCategory` imply Mathlib's `PreGaloisCategory`. -/
private theorem preGaloisOfAxioms
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] :
    PreGaloisCategory C := by
  refine {
    hasQuotientsByFiniteGroups := ?_
    monoInducesIsoOnDirectSummand := fun i _ => exists_isColimit_binaryCofan_of_mono F i }
  intro G _ _
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

/-- A finite-set-valued functor satisfying the Galois category axioms is a fibre functor in
Mathlib's sense. -/
private theorem fiberFunctorOfAxioms
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [PreGaloisCategory C] : PreGaloisCategory.FiberFunctor F := by
  have : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F FintypeCat.incl
  have : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_reflects_of_preserves F FintypeCat.incl
  refine { preservesQuotientsByFiniteGroups := ?_, reflectsIsos := ?_ }
  · intro K _ _
    obtain ⟨K', hk, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv K
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F
  · exact reflectsIsomorphisms_of_comp F FintypeCat.incl

/-- The axioms of `IsGaloisCategory` imply Mathlib's `GaloisCategory`, with `F` a fibre functor. -/
private theorem exists_galoisCategory_fiberFunctor
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] :
    ∃ h : GaloisCategory C, @PreGaloisCategory.FiberFunctor C _ h.toPreGaloisCategory F := by
  let : PreGaloisCategory C := preGaloisOfAxioms F
  let : PreGaloisCategory.FiberFunctor F := fiberFunctorOfAxioms F
  exact ⟨{ hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch.{w,v}, inferInstance⟩ }, inferInstance⟩

/-- A connected object whose fibre embeds into a fibre on which `Aut F` acts trivially is
final. -/
private theorem nonempty_isTerminal_of_injective_of_trivialAutAction
    {C : Type u} [Category.{v, u} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
    [PreGaloisCategory.FiberFunctor F] {A X : C} [PreGaloisCategory.IsConnected A] (f : A ⟶ X)
    (hinj : Function.Injective ((setValuedFiberFunctor F).map f))
    (htriv : ∀ g : Aut F, ∀ x : F.obj X, g • x = x) :
    Nonempty (IsTerminal A) := by
  let G := setValuedFiberFunctor F
  have hsub : Subsingleton (F.obj A) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) a b
    apply hinj
    calc
      F.map f a = g • F.map f a := (htriv g (F.map f a)).symm
      _ = F.map f (g • a) := PreGaloisCategory.mulAction_naturality F g f a
      _ = F.map f b := congrArg (F.map f) hg
  let : Unique (G.obj A) :=
    ⟨⟨Classical.choice (show Nonempty (G.obj A) from
      ⟨Classical.choice (inferInstance : Nonempty (F.obj A))⟩)⟩,
      fun x => hsub.elim x _⟩
  have htermF : IsTerminal (F.obj A) := by
    have htermT : IsTerminal (FintypeCat.incl.obj (F.obj A)) :=
      (Types.isTerminalEquivUnique (G.obj A)).symm inferInstance
    exact (IsTerminal.isTerminalIffObj FintypeCat.incl (F.obj A)).symm htermT
  have hmapIso : IsIso (F.map (terminal.from A)) := by
    have htop : IsTerminal (F.obj (⊤_ C)) :=
      (terminalIsTerminal (C := C)).isTerminalObj F (⊤_ C)
    rw [show F.map (terminal.from A) =
      (htermF.uniqueUpToIso htop).hom from htop.hom_ext _ _]
    infer_instance
  have : IsIso (terminal.from A) := isIso_of_reflects_iso _ F
  exact ⟨(terminalIsTerminal (C := C)).ofIso (asIso (terminal.from A)).symm⟩

/-- An object of a Galois category is a finite coproduct of final objects exactly when the
automorphism group of the fibre functor acts trivially on its fibre. -/
private theorem finiteCoproductOfTerminal_iff_trivialAutAction
    {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] (X : C) :
    IsFiniteCoproductOfTerminal X ↔
      ∀ g : Aut F, ∀ x : F.obj X, g • x = x := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  constructor
  · rintro ⟨n, A, f, hA, hc⟩ g x
    let G := setValuedFiberFunctor F
    have hcG : IsColimit (Cofan.mk (G.obj X) (fun i => G.map (f i))) :=
      isColimitCofanMkObjOfIsColimit G A f hc.some
    obtain ⟨i, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hcG x
    have hfix : g.asIso.hom.app (A i) a = a := by
      obtain ⟨hterm⟩ := hA i
      have huniq : g.asIso.hom.app (A i) = 𝟙 (F.obj (A i)) :=
        (hterm.isTerminalObj F (A i)).hom_ext _ _
      exact ConcreteCategory.congr_hom huniq a
    change g.asIso.hom.app X (F.map (f i) a) = F.map (f i) a
    have hn := NatTrans.naturality_apply g.asIso.hom (f i) a
    change g.asIso.hom.app X (F.map (f i) a) = F.map (f i) (g.asIso.hom.app (A i) a) at hn
    rwa [hfix] at hn
  · intro htriv
    obtain ⟨ι, A, f, hc, hfin, hconn⟩ :=
      IsGaloisCategory.exists_finite_coproduct_connected
        (F := setValuedFiberFunctor F) X
    let G := setValuedFiberFunctor F
    have hcG : IsColimit (Cofan.mk (G.obj X) (fun i => G.map (f i))) :=
      isColimitCofanMkObjOfIsColimit G A f hc
    have hterminal (i : ι) : Nonempty (IsTerminal (A i)) := by
      have : PreGaloisCategory.IsConnected (A i) := hconn i
      exact nonempty_isTerminal_of_injective_of_trivialAutAction F (f i)
        (Cofan.inj_injective_of_isColimit hcG i) htriv
    let : Fintype ι := Fintype.ofFinite ι
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let A' : Fin (Fintype.card ι) → C := fun j => A (e.symm j)
    let f' : (j : Fin (Fintype.card ι)) → A' j ⟶ X := fun j => f (e.symm j)
    have hc' : IsColimit (Cofan.mk X f') :=
      (Cofan.isColimitEquivOfEquiv (ε := e.symm) (Cofan.mk X f)).toFun hc
    exact ⟨Fintype.card ι, A', f', fun j => hterminal (e.symm j), ⟨hc'⟩⟩

/-- A finite continuous action of a compact group on which the kernel of a surjective quotient
map acts trivially is restricted from the quotient. -/
private theorem contAction_res_essImage_of_kernel_fixes
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [T2Space G] (f : H →ₜ* G) (hf : Function.Surjective f)
    (X : ContAction FintypeCat H)
    (hfix : ∀ k : H, k ∈ MonoidHom.ker f.toMonoidHom → ∀ x : X.obj.V, k • x = x) :
    (ContAction.res FintypeCat f).essImage X := by
  classical
  let K : Subgroup H := MonoidHom.ker f.toMonoidHom
  have hK : K ≤ (Action.ρAut X.obj).ker := by
    intro k hk
    apply Aut.ext
    ext x
    exact hfix k hk x
  let ψ : H ⧸ K →* Aut X.obj.V := QuotientGroup.lift K
    (Action.ρAut X.obj) hK
  let e : H ⧸ K ≃* G := QuotientGroup.quotientKerEquivOfSurjective
    f.toMonoidHom hf
  let θ : G →* Aut X.obj.V := ψ.comp e.symm.toMonoidHom
  have hθ (k : H) : θ (f k) = Action.ρAut X.obj k := by
    have he : e.symm (f k) = (QuotientGroup.mk k : H ⧸ K) := by
      apply e.injective
      rw [e.apply_symm_apply]
      change f.toMonoidHom k =
        (QuotientGroup.kerLift f.toMonoidHom) (QuotientGroup.mk k)
      rw [QuotientGroup.kerLift_mk]
    change ψ (e.symm (f k)) = Action.ρAut X.obj k
    rw [he]
    change (QuotientGroup.lift K (Action.ρAut X.obj) hK)
      (QuotientGroup.mk k) = Action.ρAut X.obj k
    rfl
  let A : Action FintypeCat G :=
    ⟨X.obj.V, Aut.toEnd.comp θ⟩
  have hfq : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hf f.continuous
  have hfo : IsOpenQuotientMap f :=
    MonoidHom.isOpenQuotientMap_of_isQuotientMap hfq
  have hp : IsOpenQuotientMap (fun p : H × X.obj.V => (f p.1, p.2)) :=
    hfo.prodMap IsOpenQuotientMap.id
  have hcomp :
      (fun p : G × X.obj.V => ConcreteCategory.hom (A.ρ p.1).asHom p.2) ∘
        (fun p : H × X.obj.V => (f p.1, p.2)) =
      fun p : H × X.obj.V => ConcreteCategory.hom (X.obj.ρ p.1).asHom p.2 := by
    funext p
    simp only [Function.comp_apply]
    change ConcreteCategory.hom ((Aut.toEnd (θ (f p.1))).asHom) p.2 =
      ConcreteCategory.hom (X.obj.ρ p.1).asHom p.2
    rw [hθ]
    rfl
  have hcont : Continuous (fun p : G × X.obj.V => ConcreteCategory.hom (A.ρ p.1).asHom p.2) :=
    hp.isQuotientMap.continuous_iff.mpr
      (hcomp ▸ (Action.isContinuous_def X.obj).mp X.property)
  let Y : ContAction FintypeCat G := ⟨A, (Action.isContinuous_def A).mpr hcont⟩
  have eA : (Action.res FintypeCat f.toMonoidHom).obj A ≅ X.obj := by
    refine Action.mkIso (Iso.refl _) ?_
    intro k
    ext x
    change ConcreteCategory.hom ((Aut.toEnd (θ (f k))).asHom) x =
      ConcreteCategory.hom (X.obj.ρ k).asHom x
    rw [hθ]
    rfl
  exact ⟨Y, ⟨ObjectProperty.isoMk _ eA⟩⟩

/-- A finite continuous action of a compact group is restricted from a quotient exactly when the
kernel of the quotient map acts trivially. -/
private theorem contAction_res_essImage_iff_kernel_fixes
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [T2Space G] (f : H →ₜ* G) (hf : Function.Surjective f)
    (X : ContAction FintypeCat H) :
    (ContAction.res FintypeCat f).essImage X ↔
      ∀ k : H, k ∈ MonoidHom.ker f.toMonoidHom → ∀ x : X.obj.V, k • x = x := by
  classical
  constructor
  · rintro ⟨Y, ⟨e⟩⟩ k hk x
    let eA : (Action.res FintypeCat f.toMonoidHom).obj Y.obj ≅ X.obj :=
      (ObjectProperty.ι _).mapIso e
    have hfk' : f.toMonoidHom k = 1 := MonoidHom.mem_ker.mp hk
    have hc : eA.hom.hom = eA.hom.hom ≫ (X.obj.ρ k).asHom := by
      have hc₀ := eA.hom.comm k
      change (Y.obj.ρ (f.toMonoidHom k)).asHom ≫ eA.hom.hom =
        eA.hom.hom ≫ (X.obj.ρ k).asHom at hc₀
      rw [hfk'] at hc₀
      simpa [Action.res] using hc₀
    have hρ : 𝟙 X.obj.V = (X.obj.ρ k).asHom :=
      (cancel_epi eA.hom.hom).mp ((Category.comp_id _).trans hc)
    change (ConcreteCategory.hom (X.obj.ρ k).asHom) x = x
    rw [← hρ]
    rfl
  · exact contAction_res_essImage_of_kernel_fixes f hf X

/-- Being fixed by a family of group elements transports along an isomorphism of finite
continuous actions. -/
private theorem fixes_iff_of_iso {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {ι : Type*} (φ : ι → G)
    {X Y : ContAction FintypeCat G} (e : X ≅ Y) :
    (∀ a : ι, ∀ x : X.obj.V, φ a • x = x) ↔
      ∀ a : ι, ∀ y : Y.obj.V, φ a • y = y := by
  let eA : X.obj ≅ Y.obj := (ObjectProperty.ι _).mapIso e
  let eU : X.obj.V ≅ Y.obj.V := asIso eA.hom.hom
  have hbij := (ConcreteCategory.isIso_iff_bijective eU.hom).mp inferInstance
  constructor
  · intro h g y
    obtain ⟨x, hx⟩ := hbij.2 y
    have hc := ConcreteCategory.congr_hom (eA.hom.comm (φ g)) x
    change eU.hom x = y at hx
    change eU.hom (φ g • x) = φ g • eU.hom x at hc
    rw [h g x] at hc
    rw [← hx]
    exact hc.symm
  · intro h g x
    apply hbij.1
    have hc := ConcreteCategory.congr_hom (eA.hom.comm (φ g)) x
    change eU.hom (φ g • x) = φ g • eU.hom x at hc
    rwa [h g (eU.hom x)] at hc

/-- Triviality of a finite continuous action transports along an isomorphism. -/
private theorem trivialAction_iff_of_iso {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {X Y : ContAction FintypeCat G} (e : X ≅ Y) :
    (∀ g : G, ∀ x : X.obj.V, g • x = x) ↔
      ∀ g : G, ∀ y : Y.obj.V, g • y = y :=
  fixes_iff_of_iso id e

/-- An object of the target lies in the essential image of the functor exactly when the
corresponding continuous action is restricted along the induced homomorphism. -/
private theorem essImage_iff_res_essImage
    {C : Type u} [Category.{v, u} C] {C' : Type u'} [Category.{v', u'} C']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t) (X' : C') :
    H.essImage X' ↔
      (ContAction.res FintypeCat d.hom).essImage
        ((PreGaloisCategory.functorToContAction F').obj X') := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  let A := PreGaloisCategory.functorToContAction F
  let B := PreGaloisCategory.functorToContAction F'
  let E := B.asEquivalence
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨A.obj X, ⟨d.actionIso.app X ≪≫ B.mapIso e⟩⟩
  · rintro ⟨Z, ⟨e⟩⟩
    obtain ⟨X, ⟨a⟩⟩ := Functor.EssSurj.mem_essImage A Z
    let eHX : B.obj (H.obj X) ≅ B.obj X' :=
      (d.actionIso.app X).symm ≪≫ (ContAction.res FintypeCat d.hom).mapIso a ≪≫ e
    exact ⟨X, ⟨E.unitIso.app (H.obj X) ≪≫ E.inverse.mapIso eHX ≪≫
      E.symm.counitIso.app X'⟩⟩

/-- In a profinite group an open subgroup separates a closed subgroup from a point outside it. -/
private theorem openSubgroup_separates_closedSubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (L : ClosedSubgroup G) {g : G} (hg : g ∉ L) :
    ∃ U : OpenSubgroup G, L ≤ U.toSubgroup ∧ g ∉ U := by
  have hEq := ProfiniteGrp.closedSubgroup_eq_sInf_open L
  have hg' : g ∉ (sInf {N : Subgroup G | IsOpen (N : Set G) ∧ L ≤ N} : Subgroup G) := by
    rwa [← hEq]
  by_contra hnone
  refine hg' (Subgroup.mem_sInf.mpr fun N hN => ?_)
  by_contra hgn
  exact hnone ⟨⟨N, hN.1⟩, hN.2, hgn⟩

/-- An element of a normal subgroup contained in an open subgroup fixes the base point of the
transported coset action. -/
private theorem quotientContActionSwitch_basepoint_fixed
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) {N : Subgroup G} [N.Normal]
    (hNU : N ≤ U.toSubgroup) (g : G) (hg : g ∈ N) :
    let Q0 := quotientContAction U
    let q : (quotientContActionSwitch U).obj.V :=
      (FintypeCat.uSwitchEquiv Q0.obj.V).symm (⟦1⟧ : G ⧸ U.toSubgroup)
    g • q = q := by
  dsimp only
  let Q0 := quotientContAction U
  let e := FintypeCat.uSwitchEquiv Q0.obj.V
  let : MulAction G (G ⧸ U.toSubgroup) := MulAction.quotient G U.toSubgroup
  let q : (quotientContActionSwitch U).obj.V := e.symm (⟦1⟧ : G ⧸ U.toSubgroup)
  change (FintypeCat.uSwitch.map (Q0.obj.ρ g).asHom) q = q
  apply e.injective
  rw [← FintypeCat.uSwitchEquiv_naturality]
  have hq : e q = (⟦1⟧ : G ⧸ U.toSubgroup) := Equiv.apply_symm_apply _ _
  rw [hq]
  change g • (⟦1⟧ : G ⧸ U.toSubgroup) = ⟦1⟧
  rw [MulAction.Quotient.smul_mk]
  apply QuotientGroup.eq.mpr
  simpa using U.inv_mem (hNU hg)

/-- An element of a normal subgroup contained in an open subgroup acts trivially on the whole
transported coset action. -/
private theorem quotientContActionSwitch_fixed
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) {N : Subgroup G} [N.Normal]
    (hNU : N ≤ U.toSubgroup) {g : G} (hg : g ∈ N) :
    ∀ x : (quotientContActionSwitch U).obj.V, g • x = x := by
  let Q0 := quotientContAction U
  have : MulAction.IsPretransitive G Q0.obj.V := by
    let : MulAction G (G ⧸ U.toSubgroup) := MulAction.quotient G U.toSubgroup
    exact MulAction.isPretransitive_quotient G U.toSubgroup
  have : MulAction.IsPretransitive G (quotientContActionSwitch U).obj.V :=
    pretransitive_uSwitch (A := Q0.obj)
  let q : (quotientContActionSwitch U).obj.V :=
    (FintypeCat.uSwitchEquiv Q0.obj.V).symm (⟦1⟧ : G ⧸ U.toSubgroup)
  intro x
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G q x
  have hconj : a⁻¹ * g * a ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem' g hg a
  have hqfix : (a⁻¹ * g * a) • q = q := by
    simpa [q] using quotientContActionSwitch_basepoint_fixed U hNU _ hconj
  rw [← ha, ← mul_smul, show g * a = a * (a⁻¹ * g * a) by group, mul_smul, hqfix]

/-- An element outside an open subgroup moves the base point of the transported coset action. -/
private theorem quotientContActionSwitch_not_fixed
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) {g : G} (hg : g ∉ U) :
    let Q := quotientContAction U
    let q : (quotientContActionSwitch U).obj.V :=
      (FintypeCat.uSwitchEquiv Q.obj.V).symm (⟦1⟧ : G ⧸ U.toSubgroup)
    g • q ≠ q := by
  dsimp only
  let Q0 := quotientContAction U
  let e := FintypeCat.uSwitchEquiv Q0.obj.V
  let q : (quotientContActionSwitch U).obj.V := e.symm (⟦1⟧ : G ⧸ U.toSubgroup)
  let : MulAction G (G ⧸ U.toSubgroup) := MulAction.quotient G U.toSubgroup
  have hmove : g • (⟦1⟧ : G ⧸ U.toSubgroup) ≠ ⟦1⟧ := by
    intro heq
    rw [MulAction.Quotient.smul_mk] at heq
    have hmem : g⁻¹ ∈ U.toSubgroup := by simpa using (QuotientGroup.eq.mp heq)
    exact hg (U.inv_mem_iff.mp hmem)
  change (FintypeCat.uSwitch.map (Q0.obj.ρ g).asHom) q ≠ q
  intro heq
  have hq : e q = (⟦1⟧ : G ⧸ U.toSubgroup) := Equiv.apply_symm_apply _ _
  have h' := FintypeCat.uSwitchEquiv_naturality (Q0.obj.ρ g).asHom q
  rw [hq, heq, hq] at h'
  exact hmove h'

/-- Exactness of `G″ → G′ → G → 1`: the second map is surjective, the composite is
trivial, and its kernel is the smallest closed normal subgroup containing the image of the first
map. -/
def IsExactSequence {G'' G' G : Type*}
    [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h' : G'' →ₜ* G') (h : G' →ₜ* G) : Prop :=
  Function.Surjective h ∧
    h.toMonoidHom.comp h'.toMonoidHom = 1 ∧
      MonoidHom.ker h.toMonoidHom =
        (Subgroup.normalClosure (Set.range h')).topologicalClosure

/-- An element is in the kernel of a finite continuous action exactly when it fixes every
point. -/
private theorem actionKernel_mem_iff {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (X : ContAction FintypeCat G) (g : G) :
    g ∈ (Action.ρAut X.obj).ker ↔ ∀ x : X.obj.V, g • x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · exact fun h x => ConcreteCategory.congr_hom (congrArg (fun a => a.asIso.hom) h) x
  · intro h
    apply Aut.ext
    ext x
    exact h x

/-- The kernel of a finite continuous action is closed. -/
private theorem actionKernel_isClosed {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (X : ContAction FintypeCat G) :
    IsClosed ((Action.ρAut X.obj).ker : Set G) := by
  classical
  have hstab (x : X.obj.V) : IsClosed {g : G | g • x = x} := by
    have hcont : Continuous (fun g : G => g • x) := by
      have hact := (Action.isContinuous_def X.obj).mp X.property
      exact hact.comp (continuous_id.prodMk continuous_const)
    exact isClosed_singleton.preimage hcont
  have hset : ((Action.ρAut X.obj).ker : Set G) =
      ⋂ x : X.obj.V, {g : G | g • x = x} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact actionKernel_mem_iff X g
  rw [hset]
  exact isClosed_iInter hstab

/-- Given exactness of the sequence of groups, the kernel of the second map acts trivially on a
finite continuous action exactly when the image of the first map does. -/
private theorem kernel_fixes_iff_range_fixes
    {G'' G' G : Type*}
    [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h' : G'' →ₜ* G') (h : G' →ₜ* G)
    (hcomp : h.toMonoidHom.comp h'.toMonoidHom = 1)
    (hker : MonoidHom.ker h.toMonoidHom =
      (Subgroup.normalClosure (Set.range h')).topologicalClosure)
    (X : ContAction FintypeCat G') :
    (∀ k : G', k ∈ MonoidHom.ker h.toMonoidHom →
      ∀ x : X.obj.V, k • x = x) ↔
      ∀ a : G'', ∀ x : X.obj.V, h' a • x = x := by
  let L : Subgroup G' := (Action.ρAut X.obj).ker
  have hLclosed : IsClosed (L : Set G') := actionKernel_isClosed X
  constructor
  · intro hfix a x
    refine hfix _ ?_ x
    rw [MonoidHom.mem_ker]
    simpa using congrArg (fun q : G'' →* G => q a) hcomp
  · intro hfix k hk x
    have hrange : Set.range h' ⊆ L := by
      rintro _ ⟨a, rfl⟩
      exact (actionKernel_mem_iff X _).mpr (hfix a)
    rw [hker] at hk
    exact (actionKernel_mem_iff X k).mp
      (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hrange)
        hLclosed hk) x

/-- For a surjective induced homomorphism, membership in the essential image is equivalent to the
kernel acting trivially on the fibre. -/
private theorem essImage_iff_d_kernel_fixes
    {C : Type u} [Category.{v, u} C]
    {C' : Type u'} [Category.{v', u'} C']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t)
    (hd : Function.Surjective d.hom) (X' : C') :
    H.essImage X' ↔
      ∀ k : Aut F', k ∈ MonoidHom.ker d.hom.toMonoidHom →
        ∀ x : ((PreGaloisCategory.functorToContAction F').obj X').obj.V,
          k • x = x :=
  (essImage_iff_res_essImage F F' H t d X').trans
    (contAction_res_essImage_iff_kernel_fixes d.hom hd _)

/-- The image of an object under the second functor is a finite coproduct of final objects exactly
when the second induced homomorphism acts trivially on the fibre of the object. -/
private theorem terminalCoproduct_iff_dprime_fixes
    {C' : Type u'} [Category.{v', u'} C']
    {C'' : Type u''} [Category.{v'', u''} C'']
    (F' : C' ⥤ FintypeCat.{w}) (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H' : C' ⥤ C'') (t' : H' ⋙ F'' ≅ F')
    (d' : GaloisFunctorData F' F'' H' t') (X' : C') :
    IsFiniteCoproductOfTerminal (H'.obj X') ↔
      ∀ a : Aut F'', ∀ x : ((PreGaloisCategory.functorToContAction F').obj X').obj.V,
        d'.hom a • x = x := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F''
  rw [finiteCoproductOfTerminal_iff_trivialAutAction F'' (H'.obj X')]
  have hIso := (trivialAction_iff_of_iso (d'.actionIso.app X')).symm
  change (∀ a : Aut F'', ∀ x : (F''.obj (H'.obj X')).obj, a • x = x) ↔
    ∀ a : Aut F'', ∀ x : (F'.obj X').obj, d'.hom a • x = x at hIso
  exact hIso

/-- Surjectivity of the induced homomorphism is equivalent to full faithfulness of the functor. -/
@[sga "1 V 6.9" "(i) ⇔ (iii)"]
private theorem surjective_iff_fullyFaithful
    {C : Type u} [Category.{v, u} C]
    {C' : Type u'} [Category.{v', u'} C']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (hH : exactFunctor C C' H) (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t) :
    Function.Surjective d.hom ↔ Nonempty H.FullyFaithful := by
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  let : PreservesFiniteLimits H := (exactFunctor_iff H).mp hH |>.1
  exact (surjective_inducedHom_tfae F F' H hH t d (⊤_ C) (⊤_ C') terminalIsTerminal
    terminalIsTerminal (terminalIsTerminal.isTerminalObj H (⊤_ C))).out 1 2

/-- If the essential image of `H` is cut out by triviality of the action of the image of `h'`,
the kernel of the induced homomorphism lies in the closed normal subgroup generated by that
image. -/
private theorem ker_le_topologicalClosure_normalClosure_range
    {C : Type u} [Category.{v, u} C] {C' : Type u'} [Category.{v', u'} C']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (d : GaloisFunctorData F F' H t)
    (hsurj : Function.Surjective d.hom)
    {G'' : Type*} [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']
    (h' : G'' →ₜ* Aut F')
    (hP : ∀ X' : C', H.essImage X' ↔
      ∀ a : G'', ∀ x : ((PreGaloisCategory.functorToContAction F').obj X').obj.V, h' a • x = x) :
    MonoidHom.ker d.hom.toMonoidHom ≤
      (Subgroup.normalClosure (Set.range h')).topologicalClosure := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  let B := PreGaloisCategory.functorToContAction F'
  let N : Subgroup (Aut F') := (Subgroup.normalClosure (Set.range h')).topologicalClosure
  have hNnormal : N.Normal := Subgroup.is_normal_topologicalClosure _
  intro k hk
  by_contra hkn
  let L : ClosedSubgroup (Aut F') := ⟨N, Subgroup.isClosed_topologicalClosure _⟩
  obtain ⟨U, hNU, hkU⟩ := openSubgroup_separates_closedSubgroup L hkn
  have hrangeN (a : G'') : h' a ∈ N :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨a, rfl⟩)
  let Q := quotientContActionSwitch U
  obtain ⟨X', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage B Q
  have hQfix (a : G'') : ∀ x : Q.obj.V, h' a • x = x :=
    quotientContActionSwitch_fixed U hNU (g := h' a) (hrangeN a)
  obtain ⟨Y, ⟨eY⟩⟩ := (essImage_iff_res_essImage F F' H t d X').mp
    ((hP X').mpr ((fixes_iff_of_iso h' e).mpr hQfix))
  have hQker := (contAction_res_essImage_iff_kernel_fixes d.hom hsurj Q).mp ⟨Y, ⟨eY ≪≫ e⟩⟩
  let Q0 := quotientContAction U
  let q : Q.obj.V := (FintypeCat.uSwitchEquiv Q0.obj.V).symm (⟦1⟧ : Aut F' ⧸ U.toSubgroup)
  have hnot : k • q ≠ q := by
    simpa [q] using quotientContActionSwitch_not_fixed U hkU (g := k)
  exact hnot (hQker k hk q)

/-- If the induced homomorphism is surjective and the essential image of `H` consists of the
objects sent by `H'` to finite coproducts of final objects, the induced sequence is exact. -/
private theorem isExactSequence_of_essImage_iff
    {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C'']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (d : GaloisFunctorData F F' H t)
    (d' : GaloisFunctorData F' F'' H' t')
    (hsurj : Function.Surjective d.hom)
    (hcrit : ∀ X' : C', H.essImage X' ↔ IsFiniteCoproductOfTerminal (H'.obj X')) :
    IsExactSequence d'.hom d.hom := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F''
  have hcomp : d.hom.toMonoidHom.comp d'.hom.toMonoidHom = 1 :=
    (comp_hom_eq_one_iff_forall_isFiniteCoproductOfTerminal F F' F'' H H' t t' d d').mpr
      fun X => (hcrit (H.obj X)).mp ⟨X, ⟨Iso.refl _⟩⟩
  have hkerClosed : IsClosed (MonoidHom.ker d.hom.toMonoidHom : Set (Aut F')) := by
    change IsClosed {g : Aut F' | d.hom.toMonoidHom g = 1}
    exact isClosed_singleton.preimage d.hom.continuous
  have hNker : (Subgroup.normalClosure (Set.range d'.hom)).topologicalClosure ≤
      MonoidHom.ker d.hom.toMonoidHom := by
    apply Subgroup.topologicalClosure_minimal (Subgroup.normalClosure (Set.range d'.hom))
    · apply Subgroup.normalClosure_le_normal
      rintro _ ⟨a, rfl⟩
      have hh := congrArg (fun q : Aut F'' →* Aut F => q a) hcomp
      change d.hom.toMonoidHom (d'.hom a) = 1
      simpa using hh
    · exact hkerClosed
  exact ⟨hsurj, hcomp, le_antisymm (ker_le_topologicalClosure_normalClosure_range F F' H t d
    hsurj d'.hom fun X' => (hcrit X').trans (terminalCoproduct_iff_dprime_fixes F' F'' H' t' d' X'))
    hNker⟩

/-- For a surjective induced homomorphism, the target of an epimorphism out of an object in the
image of `H` lies in the essential image of `H`. -/
private theorem essImage_of_epi
    {C : Type u} [Category.{v, u} C] {C' : Type u'} [Category.{v', u'} C']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (d : GaloisFunctorData F F' H t)
    (hsurj : Function.Surjective d.hom) {X : C} {X' : C'} (f : H.obj X ⟶ X') [Epi f] :
    H.essImage X' := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  let B := PreGaloisCategory.functorToContAction F'
  have hsurjB : Function.Surjective (B.map f).hom.hom := by
    change Function.Surjective (F'.map f).hom
    exact PreGaloisCategory.surjective_on_fiber_of_epi F' f
  have hkerFixTarget : ∀ k : Aut F', k ∈ MonoidHom.ker d.hom.toMonoidHom →
      ∀ y : (B.obj X').obj.V, k • y = y := by
    intro k hk y
    obtain ⟨x, hx⟩ := hsurjB y
    have hcomm := ConcreteCategory.congr_hom ((B.map f).hom.comm k) x
    change (B.map f).hom.hom (k • x) = k • (B.map f).hom.hom x at hcomm
    rw [← hx, ← hcomm,
      (essImage_iff_d_kernel_fixes F F' H t d hsurj (H.obj X)).mp ⟨X, ⟨Iso.refl _⟩⟩ k hk x]
  exact (essImage_iff_d_kernel_fixes F F' H t d hsurj X').mpr hkerFixTarget

/-- **Stacks 0BS9.** For composable exact functors between Galois categories, exactness of the
induced sequence of automorphism groups is equivalent both to the essential-image criterion and to
its epimorphic-cover variant. -/
@[stacks 0BS9]
theorem galoisExact_iff_categorical_conditions
    {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C'']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (_hH : exactFunctor C C' H) (_hH' : exactFunctor C' C'' H')
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (d : GaloisFunctorData F F' H t)
    (d' : GaloisFunctorData F' F'' H' t') :
    List.TFAE
      [ IsExactSequence d'.hom d.hom,
        Nonempty H.FullyFaithful ∧
          ∀ X' : C',
            (H.essImage X' ↔ IsFiniteCoproductOfTerminal (H'.obj X')),
        Nonempty H.FullyFaithful ∧
          (∀ X : C, IsFiniteCoproductOfTerminal ((H ⋙ H').obj X)) ∧
          (∀ X' : C', IsFiniteCoproductOfTerminal (H'.obj X') →
            ∃ (X : C) (f : H.obj X ⟶ X'), Epi f) ] := by
  classical
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F'
  obtain ⟨_, _⟩ := exists_galoisCategory_fiberFunctor F''
  let : PreservesFiniteLimits H := (exactFunctor_iff H).mp _hH |>.1
  have hsff : Function.Surjective d.hom ↔ Nonempty H.FullyFaithful :=
    surjective_iff_fullyFaithful F F' H _hH t d
  let B := PreGaloisCategory.functorToContAction F'
  tfae_have h12 : 1 → 2 := by
    rintro ⟨hsurj, hcomp, hker⟩
    refine ⟨hsff.mp hsurj, ?_⟩
    intro X'
    calc
      H.essImage X' ↔
          ∀ k : Aut F', k ∈ MonoidHom.ker d.hom.toMonoidHom →
            ∀ x : (B.obj X').obj.V, k • x = x :=
        essImage_iff_d_kernel_fixes F F' H t d hsurj X'
      _ ↔ ∀ a : Aut F'', ∀ x : (B.obj X').obj.V, d'.hom a • x = x :=
        kernel_fixes_iff_range_fixes d'.hom d.hom hcomp hker (B.obj X')
      _ ↔ IsFiniteCoproductOfTerminal (H'.obj X') :=
        (terminalCoproduct_iff_dprime_fixes F' F'' H' t' d' X').symm
  tfae_have h21 : 2 → 1 := fun ⟨hff, hcrit⟩ =>
    isExactSequence_of_essImage_iff F F' F'' H H' t t' d d' (hsff.mpr hff) hcrit
  tfae_have h23 : 2 → 3 := by
    rintro ⟨hff, hcrit⟩
    refine ⟨hff, fun X => (hcrit (H.obj X)).mp ⟨X, ⟨Iso.refl _⟩⟩, fun X' hterm => ?_⟩
    rcases (hcrit X').mpr hterm with ⟨X, ⟨e⟩⟩
    exact ⟨X, e.hom, inferInstance⟩
  tfae_have h31 : 3 → 1 := by
    rintro ⟨hff, hfinite, hcover⟩
    have hsurj : Function.Surjective d.hom := hsff.mpr hff
    refine isExactSequence_of_essImage_iff F F' F'' H H' t t' d d' hsurj
      fun X' => ⟨fun he => ?_, fun hterm => ?_⟩
    · obtain ⟨X, ⟨e⟩⟩ := he
      exact (terminalCoproduct_iff_dprime_fixes F' F'' H' t' d' X').mpr
        ((fixes_iff_of_iso d'.hom (B.mapIso e)).mp
          ((terminalCoproduct_iff_dprime_fixes F' F'' H' t' d' (H.obj X)).mp (hfinite X)))
    · obtain ⟨X, f, hf⟩ := hcover X' hterm
      exact essImage_of_epi F F' H t d hsurj f
  tfae_finish

/-- **Stacks 0BS9.** For composable exact functors between Galois categories, exactness of the
induced sequence of automorphism groups is equivalent both to the essential-image criterion and to
its epimorphic-cover variant.

This is the form of the statement in which no part of the functoriality data is assumed: the two
continuous homomorphisms are the ones produced from the fibre-functor isomorphisms `t` and `t'`,
whose continuity and whose 2-isomorphisms of the two functoriality squares are constructed by
`CategoryTheory.galoisFunctorDataOfFiberIso`. -/
@[stacks 0BS9]
theorem galoisExact_iff_categorical_conditions_of_fiberIso
    {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C'']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (hH : exactFunctor C C' H) (hH' : exactFunctor C' C'' H')
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F') :
    List.TFAE
      [ IsExactSequence (galoisFunctorDataOfFiberIso F' F'' H' t').hom
          (galoisFunctorDataOfFiberIso F F' H t).hom,
        Nonempty H.FullyFaithful ∧
          ∀ X' : C',
            (H.essImage X' ↔ IsFiniteCoproductOfTerminal (H'.obj X')),
        Nonempty H.FullyFaithful ∧
          (∀ X : C, IsFiniteCoproductOfTerminal ((H ⋙ H').obj X)) ∧
          (∀ X' : C', IsFiniteCoproductOfTerminal (H'.obj X') →
            ∃ (X : C) (f : H.obj X ⟶ X'), Epi f) ] :=
  galoisExact_iff_categorical_conditions F F' F'' H H' hH hH' t t'
    (galoisFunctorDataOfFiberIso F F' H t) (galoisFunctorDataOfFiberIso F' F'' H' t')

end Stacks.FundamentalGroup
