module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Spectral.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.AboveTheDimension
public import StacksFrontier.Topology.Sober.Soberification
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a Noetherian topological space above its dimension

Grothendieck's vanishing theorem says that the cohomology of an abelian sheaf on a Noetherian
topological space vanishes above the Krull dimension of the space. A Noetherian space need not be
sober, but its soberification is a Noetherian sober space, hence a spectral space, with the same
lattice of opens and the same Krull dimension; so Grothendieck vanishing for Noetherian spaces is
vanishing above the dimension for spectral spaces, transported along that identification.

## Main definitions

* `Stacks.CohomologyVanishing.soberificationOpensOrderIso`: the order isomorphism
  `Opens (Soberification X) ≃o Opens X`.
* `Stacks.CohomologyVanishing.sheafEquivOfOpensOrderIso`: the equivalence between the categories
  of abelian sheaves of two spaces induced by an order isomorphism of their lattices of opens.
* `Stacks.CohomologyVanishing.constantSheafIsoOfOpensOrderIso`: that equivalence carries the
  constant sheaf to the constant sheaf.

## Main results

* `Stacks.CohomologyVanishing.spectralSpace_soberification`: the soberification of a Noetherian
  space is a spectral space.
* `Stacks.CohomologyVanishing.topologicalKrullDim_soberification`: the soberification has the same
  topological Krull dimension as the space.
* `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_soberification`: vanishing of
  abelian sheaf cohomology in a degree on the soberification implies it on the space.
* `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace`: Grothendieck
  vanishing for Noetherian spaces, with vanishing above the dimension for spectral spaces as a
  hypothesis, at independent coefficient and `Ext` universes.
* `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_eq_zero`: the
  dimension-zero case.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant abelian
sheaf `ℤ` on the site of opens, and vanishing is expressed as `Subsingleton`. The natural-number
bound of the source is compared with the `WithBot ℕ∞`-valued `topologicalKrullDim`.

`HasExt` presupposes that the category is abelian, which for sheaves on a site presupposes
sheafification, so the sheafification and `Ext` data of `Soberification X` are hypotheses of the
statements that mention `Ext` there. They are always available: the sheafification is
`hasSheafify_of_opensOrderIso` applied to `soberificationOpensOrderIso`, and `HasExt` is
`HasExt.standard`. The `Ext`-universe of the soberification is independent of the one on `X`.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [A. Grothendieck, *Sur quelques points d'algèbre homologique*, Theorem 3.6.5][Tohoku]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

namespace Stacks.CohomologyVanishing

attribute [local instance] HasDerivedCategory.standard

universe u w w' z

/-! ### Sieves on a lattice of opens, and order isomorphisms between such lattices -/

section Sites

/-- A sieve on an open `U` of a topological space is a covering sieve exactly when the supremum
of the domains of its arrows is `U`. -/
private theorem soberTransport_covering_iff_iSup
    {X : Type u} [TopologicalSpace X] {U : Opens X} {S : Sieve U} :
    S ∈ Opens.grothendieckTopology X U ↔
      (⨆ i : Σ V : Opens X, {f : V ⟶ U // S f}, i.1) = U := by
  constructor
  · intro h
    refine le_antisymm (iSup_le fun i => i.2.1.le) fun x hx => ?_
    rw [Opens.mem_iSup]
    obtain ⟨V, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology (T := X)).mp h x hx
    exact ⟨⟨V, f, hf⟩, hxV⟩
  · intro h
    apply (Opens.mem_grothendieckTopology (T := X)).mpr
    intro x hx
    have hx' : x ∈ (⨆ i : Σ V : Opens X, {f : V ⟶ U // S f}, i.1) := h.symm ▸ hx
    obtain ⟨⟨V, f, hf⟩, hxV⟩ := Opens.mem_iSup.mp hx'
    exact ⟨V, f, hf, hxV⟩

/-- An order isomorphism of lattices of opens carries the supremum of the domains of a sieve to
the supremum of the domains of the pushed-forward sieve. -/
private theorem soberTransport_iSup_functorPushforward
    {X : Type u} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y) {U : Opens X} (S : Sieve U) :
    (⨆ i : Σ V : Opens Y,
      {f : V ⟶ e U // (S.functorPushforward e.equivalence.functor) f}, i.1) =
      e (⨆ i : Σ V : Opens X, {f : V ⟶ U // S f}, i.1) := by
  rw [e.map_iSup]
  refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
  · obtain ⟨V, f, hf⟩ := i
    have h : S (e.equivalence.inverse.map f ≫ e.equivalence.unitInv.app U) :=
      (Sieve.mem_functorPushforward_functor).mp hf
    have hle : e.symm V ≤ ⨆ i : Σ W : Opens X, {g : W ⟶ U // S g}, i.1 :=
      le_iSup_of_le ⟨e.symm V, e.equivalence.inverse.map f ≫
        e.equivalence.unitInv.app U, h⟩ le_rfl
    simpa only [OrderIso.apply_symm_apply, e.map_iSup] using e.monotone hle
  · obtain ⟨V, f, hf⟩ := i
    have h : (S.functorPushforward e.equivalence.functor)
        (e.equivalence.functor.map f) :=
      Sieve.image_mem_functorPushforward e.equivalence.functor S hf
    exact le_iSup_of_le ⟨e V, e.equivalence.functor.map f, h⟩ le_rfl

/-- An order isomorphism between the lattices of opens of two topological spaces is a dense
subsite for the open-cover topologies. -/
theorem isDenseSubsite_of_opensOrderIso
    {X : Type u} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y) :
    e.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
  refine { functorPushforward_mem_iff := ?_ }
  intro U S
  rw [soberTransport_covering_iff_iSup, soberTransport_covering_iff_iSup]
  change (⨆ i : Σ V : Opens Y,
    {f : V ⟶ e U // (S.functorPushforward e.equivalence.functor) f}, i.1) = e U ↔
      (⨆ i : Σ V : Opens X, {f : V ⟶ U // S f}, i.1) = U
  rw [soberTransport_iSup_functorPushforward e S]
  exact e.injective.eq_iff

/-- Sheafification of `AddCommGrpCat`-valued presheaves transports along an order isomorphism of
lattices of opens. -/
theorem hasSheafify_of_opensOrderIso
    {X : Type u} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y)
    (h : e.equivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{w}] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
  e.equivalence.hasSheafify
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) AddCommGrpCat.{w}

/-- The equivalence of categories of abelian sheaves induced by an order isomorphism of lattices
of opens. -/
noncomputable def sheafEquivOfOpensOrderIso
    {X : Type u} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y)
    (h : e.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} ≌
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w} :=
  have inst : ∀ T : (Opens Y)ᵒᵖ, Limits.HasInitial
      (StructuredArrow T e.equivalence.functor.op) := fun T =>
    (mkInitialOfLeftAdjoint e.equivalence.functor.op
      e.equivalence.op.symm.toAdjunction T).hasInitial
  have : ∀ T : (Opens Y)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow T e.equivalence.functor.op) AddCommGrpCat.{w} := fun T =>
    have := inst T
    ⟨fun _ => inferInstance⟩
  Functor.IsDenseSubsite.sheafEquiv
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    e.equivalence.functor AddCommGrpCat.{w}

/-- The equivalence `sheafEquivOfOpensOrderIso` carries the constant sheaf to the constant
sheaf. -/
noncomputable def constantSheafIsoOfOpensOrderIso
    {X : Type u} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y)
    (h : e.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{w}]
    (A : AddCommGrpCat.{w}) :
    (sheafEquivOfOpensOrderIso e h).functor.obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj A) ≅
      (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).obj A :=
  have inst : ∀ T : (Opens Y)ᵒᵖ, Limits.HasInitial
      (StructuredArrow T e.equivalence.functor.op) := fun T =>
    (mkInitialOfLeftAdjoint e.equivalence.functor.op
      e.equivalence.op.symm.toAdjunction T).hasInitial
  have : ∀ T : (Opens Y)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow T e.equivalence.functor.op) AddCommGrpCat.{w} := fun T =>
    have := inst T
    ⟨fun _ => inferInstance⟩
  (equivCommuteConstant
    (Opens.grothendieckTopology X) AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) e.equivalence.functor
    (Limits.isTerminalTop (α := Opens X))
    (by
      change Limits.IsTerminal (e ⊤)
      simpa only [e.map_top] using (Limits.isTerminalTop (α := Opens Y)))).app A

end Sites

/-! ### Transport of `Ext`-vanishing along isomorphisms and exact equivalences -/

section Ext

/-- `Ext` out of isomorphic objects: if `Ext A D n` is a subsingleton and `A ≅ B`, then so is
`Ext B D n`. -/
theorem subsingleton_ext_of_iso_source
    {C : Type u} [Category C] [Abelian C] [HasExt.{w} C]
    {A B D : C} (i : A ≅ B) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{w} A D n)) :
    Subsingleton (Abelian.Ext.{w} B D n) := by
  refine ⟨fun x y => ?_⟩
  have hxy : (Abelian.Ext.mk₀ i.hom).comp x (zero_add n) =
      (Abelian.Ext.mk₀ i.hom).comp y (zero_add n) := Subsingleton.elim _ _
  have hxy' := congrArg (fun t : Abelian.Ext A D n =>
    (Abelian.Ext.mk₀ i.inv).comp t (zero_add n)) hxy
  simpa [Abelian.Ext.mk₀_comp_mk₀_assoc, i.inv_hom_id] using hxy'

/-- `Ext` into isomorphic objects: if `Ext X A n` is a subsingleton and `A ≅ B`, then so is
`Ext X B n`. -/
theorem subsingleton_ext_of_iso_target
    {C : Type u} [Category C] [Abelian C]
    {A B X : C} (i : A ≅ B) (n : ℕ)
    [HasExt.{w} C] (h : Subsingleton (Abelian.Ext.{w} X A n)) :
    Subsingleton (Abelian.Ext.{w} X B n) := by
  refine ⟨fun x y => ?_⟩
  have hxy : x.comp (Abelian.Ext.mk₀ i.inv) (add_zero n) =
      y.comp (Abelian.Ext.mk₀ i.inv) (add_zero n) := Subsingleton.elim _ _
  have hxy' := congrArg (fun t : Abelian.Ext X A n =>
    t.comp (Abelian.Ext.mk₀ i.hom) (add_zero n)) hxy
  simpa [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, i.inv_hom_id] using hxy'

/-- An additive equivalence of abelian categories is a localized equivalence for the
quasi-isomorphisms of cochain complexes. -/
theorem isLocalizedEquivalence_mapHomologicalComplex_of_equivalence
    {C : Type u} {D : Type z} [Category C] [Category D]
    [Abelian C] [Abelian D] (E : C ≌ D) [E.functor.Additive] :
    (E.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence := by
  let Φ := E.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)
  have : Φ.functor.IsEquivalence := by
    change (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
    exact (E.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ
  have heq : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) =
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)).inverseImage Φ.functor := by
    ext K L f
    change QuasiIso f ↔ QuasiIso ((E.functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f E.functor).symm
  have hmap : HomologicalComplex.quasiIso D (ComplexShape.up ℤ) ≤
      ((HomologicalComplex.quasiIso D (ComplexShape.up ℤ)).inverseImage Φ.functor).map
        Φ.functor := by
    rw [MorphismProperty.map_inverseImage_eq_of_isEquivalence]
  simpa only [heq] using hmap

/-- The bijection on `Ext` induced by an additive equivalence of abelian categories. -/
noncomputable def extEquivOfEquivalence
    {C : Type u} {D : Type z} [Category C] [Category D]
    [Abelian C] [Abelian D] (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Abelian.Ext.{w} X Y n ≃
      Abelian.Ext.{w'} (E.functor.obj X) (E.functor.obj Y) n :=
  have _ : (E.functor.mapDerivedCategory).IsEquivalence :=
    (isLocalizedEquivalence_mapHomologicalComplex_of_equivalence E).isEquivalence
  let FC := E.functor.mapDerivedCategory
  let A := (DerivedCategory.singleFunctor C 0).obj X
  let B := (DerivedCategory.singleFunctor C 0).obj Y
  let A' := (DerivedCategory.singleFunctor D 0).obj (E.functor.obj X)
  let B' := (DerivedCategory.singleFunctor D 0).obj (E.functor.obj Y)
  let iA : FC.obj A ≅ A' := (E.functor.mapDerivedCategorySingleFunctor 0).app X
  let iB : FC.obj (B⟦(n : ℤ)⟧) ≅ B'⟦(n : ℤ)⟧ :=
    (FC.commShiftIso (n : ℤ)).app B ≪≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).mapIso
        ((E.functor.mapDerivedCategorySingleFunctor 0).app Y)
  let ff := FC.asEquivalence.fullyFaithfulFunctor
  (Abelian.Ext.homEquiv).trans
    ((ff.homEquiv (X := A) (Y := B⟦(n : ℤ)⟧)).trans
      ((Iso.homCongr iA iB).trans (Abelian.Ext.homEquiv).symm))

/-- `Ext`-vanishing transports along an additive equivalence of abelian categories: if
`Ext A (E⁻¹ F) n` is a subsingleton then so is `Ext (E A) F n`. -/
theorem subsingleton_ext_of_equivalence
    {C : Type u} {D : Type z} [Category C] [Category D]
    [Abelian C] [Abelian D] (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D] (A : C) (F : D) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{w} A (E.inverse.obj F) n)) :
    Subsingleton (Abelian.Ext.{w'} (E.functor.obj A) F n) :=
  have h₁ : Subsingleton (Abelian.Ext.{w'} (E.functor.obj A)
      (E.functor.obj (E.inverse.obj F)) n) :=
    ((extEquivOfEquivalence E A (E.inverse.obj F) n).subsingleton_congr).mp h
  subsingleton_ext_of_iso_target (E.counitIso.app F) n h₁

end Ext

/-! ### The soberification of a Noetherian space -/

section Soberification

variable {X : Type u} [TopologicalSpace X]

/-- The order isomorphism `Opens (Soberification X) ≃o Opens X`. On underlying sets it is
`V ↦ c ⁻¹' V` for the canonical map `c : X ⟶ Soberification X`. -/
@[sga "4 IV 4.2.1"]
def soberificationOpensOrderIso : Opens (Soberification X) ≃o Opens X where
  toEquiv := Soberification.openEquiv
  map_rel_iff' := by
    intro V W
    constructor
    · intro h
      refine inf_eq_left.mp (Soberification.openEquiv.injective ?_)
      rw [Soberification.openEquiv_inf, inf_eq_left.mpr h]
    · intro h
      refine inf_eq_left.mp ?_
      rw [← Soberification.openEquiv_inf, inf_eq_left.mpr h]

/-- The soberification of a Noetherian space is a spectral space. -/
theorem spectralSpace_soberification [NoetherianSpace X] :
    SpectralSpace (Soberification X) := by
  have hnoeth : NoetherianSpace (Soberification X) :=
    (soberificationOpensOrderIso (X := X)).strictMono.wellFoundedGT
  have : CompactSpace (Soberification X) := NoetherianSpace.compactSpace _
  have : PrespectralSpace (Soberification X) := instPrespectralSpaceOfNoetherianSpace
  have : QuasiSeparatedSpace (Soberification X) := NoetherianSpace.to_quasiSeparatedSpace
  exact SpectralSpace.mk

/-- The soberification of `X` has the same topological Krull dimension as `X`. -/
theorem topologicalKrullDim_soberification :
    topologicalKrullDim (Soberification X) = topologicalKrullDim X := by
  let _ : PartialOrder (Soberification X) := specializationOrder (Soberification X)
  let e : IrreducibleCloseds X ≃o Soberification X :=
    { toFun := fun S => ⟨S.carrier, S.isIrreducible', S.isClosed'⟩
      invFun := fun Z => ⟨Z.carrier, Z.isIrreducible', Z.isClosed'⟩
      left_inv := by intro S; cases S; rfl
      right_inv := by intro Z; cases Z; rfl
      map_rel_iff' := by
        intro S T
        change (⟨T.carrier, T.isIrreducible', T.isClosed'⟩ : Soberification X) ⤳
          (⟨S.carrier, S.isIrreducible', S.isClosed'⟩ : Soberification X) ↔
            (S : Set X) ⊆ (T : Set X)
        rw [specializes_iff_mem_closure, Soberification.closure_singleton]
        rfl }
  exact Order.krullDim_eq_of_orderIso
    ((irreducibleSetEquivPoints (α := Soberification X)).trans e.symm)

end Soberification

/-! ### Grothendieck vanishing -/

/-- If in degree `p` the cohomology of every abelian sheaf on `Soberification X` vanishes, then so
does the cohomology of every abelian sheaf on `X`. The `Ext`-universe on the soberification is
independent of the one on `X`. -/
theorem subsingleton_sheafCohomology_of_soberification
    {X : Type u} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    [HasSheafify (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w}]
    [HasExt.{z} (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w})]
    {p : ℕ}
    (hsober : ∀ G : Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w},
      Subsingleton (Sheaf.H.{z, w, u, u} G p))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    Subsingleton (Sheaf.H.{w', w, u, u} F p) := by
  classical
  let e := soberificationOpensOrderIso (X := X)
  let E : Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w} ≌
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
    sheafEquivOfOpensOrderIso e (isDenseSubsite_of_opensOrderIso e)
  have : HasBinaryProducts
      (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w}) := inferInstance
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.functor := inferInstance
  have : E.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : E.functor.Additive := E.functor.additive_of_preserves_binary_products
  exact subsingleton_ext_of_iso_source
    (constantSheafIsoOfOpensOrderIso e (isDenseSubsite_of_opensOrderIso e)
      (AddCommGrpCat.of (ULift.{w} ℤ))) p
    (subsingleton_ext_of_equivalence E
      ((constantSheaf (Opens.grothendieckTopology (Soberification X))
        AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) F p
      (hsober (E.inverse.obj F)))

/-- Let `X` be a Noetherian topological space of topological Krull dimension at most `d`, let `F`
be an abelian sheaf on `X`, and let `hspectral` be vanishing above the dimension on spectral
spaces. Then `H^p(X, F) = 0` for every `p > d`. -/
theorem subsingleton_sheafCohomology_of_noetherianSpace
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    [HasSheafify (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w}]
    [hext : HasExt.{z}
      (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w})]
    (hspectral : ∀ (Y : Type u) [TopologicalSpace Y] [SpectralSpace Y]
      (_hs : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{w})
      (_he : HasExt.{z} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}))
      (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}) (e q : ℕ),
      topologicalKrullDim Y ≤ e → e < q → Subsingleton (Sheaf.H.{z, w, u, u} G q))
    {d p : ℕ} (hdim : topologicalKrullDim X ≤ d) (hp : d < p)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    Subsingleton (Sheaf.H.{w', w, u, u} F p) := by
  have hspec : SpectralSpace (Soberification X) := spectralSpace_soberification
  refine subsingleton_sheafCohomology_of_soberification (fun G => ?_) F
  refine hspectral (Soberification X) inferInstance hext G d p ?_ hp
  rwa [topologicalKrullDim_soberification]

/-- If `X` is a Noetherian topological space of topological Krull dimension `0` and `F` is an
abelian sheaf on `X`, then `H^p(X, F) = 0` for every `p > 0`. -/
@[stacks 02UZ "dimension zero"]
theorem subsingleton_sheafCohomology_of_noetherianSpace_of_dim_eq_zero
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    (hdim : topologicalKrullDim X = ((0 : ℕ) : WithBot ℕ∞)) {p : ℕ} (hp : 0 < p)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    Subsingleton (Sheaf.H.{w', w, u, u} F p) := by
  have hspec : SpectralSpace (Soberification X) := spectralSpace_soberification
  have hsheafify : HasSheafify (Opens.grothendieckTopology (Soberification X))
      AddCommGrpCat.{w} :=
    hasSheafify_of_opensOrderIso (soberificationOpensOrderIso (X := X))
      (isDenseSubsite_of_opensOrderIso (soberificationOpensOrderIso (X := X)).symm)
  have hext := HasExt.standard
    (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{w})
  refine subsingleton_sheafCohomology_of_soberification (fun G => ?_) F
  refine cohomology_subsingleton_of_topologicalKrullDim_eq_zero G p ?_ hp
  rwa [topologicalKrullDim_soberification]

end Stacks.CohomologyVanishing

end
