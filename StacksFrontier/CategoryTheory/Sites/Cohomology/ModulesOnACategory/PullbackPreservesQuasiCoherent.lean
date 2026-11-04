module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects

/-!
# Derived pullback along a morphism of ringed topoi and cartesian objects

Let `C` and `C'` be categories viewed as sites with the chaotic topology and let `O : Cᵒᵖ ⥤
RingCat` and `O' : C'ᵒᵖ ⥤ RingCat` be sheaves of rings on them. A functor `F : C' ⥤ C` together
with a map of sheaves of rings `φ : F⁻¹O ⟶ O'`, that is a ring homomorphism `O(F U') ⟶ O'(U')`
for every object `U'` of `C'`, natural in `U'`, is the datum of a morphism of ringed topoi
`g : (Sh(C'), O') → (Sh(C), O)`. Its derived pullback `Lg^* : D(O) ⥤ D(O')` carries the cartesian
objects `QC(O)` into `QC(O')`.

The mechanism is this. Over an object `U'` of `C'` the derived sections of `Lg^*K` are
`RΓ(F U', K) ⊗^L_{O(F U')} O'(U')`. A morphism `a' : V' ⟶ U'` of `C'ᵒᵖ` gives a commuting square
of rings, the two restrictions of `O` and `O'` against the two structure maps, so going round it
by derived base change either way agrees; the cartesian condition for `Lg^*K` along `a'` is then
the base change along the structure map at `U'` of the cartesian condition for `K` along `F a'`,
conjugated by isomorphisms.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dRestrictScalars`: derived
  restriction of scalars along a ring homomorphism.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.StructureBaseChange`: derived base
  change along the structure maps `O(F U') ⟶ O'(U')`, one for each object of `C'`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.baseChangeSquare`: the two ways round
  the base-change square of a morphism of `C'ᵒᵖ` agree.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.DerivedPullbackData`: the derived
  pullback `Lg^*` together with the computation of its derived sections.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.qcPullback`: the induced functor
  `QC(O) ⥤ QC(O')`.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dRestrictScalarsSquare`: a commuting
  square of ring homomorphisms induces a commuting square of derived restrictions of scalars.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.comparison_Lpullback`: the canonical
  comparison map of `Lg^*K` is the base change along the structure map of the canonical
  comparison map of `K`, conjugated by the base-change square and the computation of the derived
  sections of `Lg^*K`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.isQC_Lpullback`: if the derived
  sections of `K` are cartesian then so are those of `Lg^*K`.

## Implementation notes

The cartesian condition is `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.IsQC`, taken
relative to an arbitrary derived base-change datum on `O` and on `O'`, as in the equivalence of
quasi-coherent derived modules and in the study of morphisms over an object; the canonical datum
of `Stacks.ModulesOnACategory.CartesianObjects.IsCartesian` is one such.

The derived pullback `Lg^*` is not constructed here. It is carried as the datum
`DerivedPullbackData`, whose field `sectionsIso` is the computation `RΓ(U', Lg^*K) ≅ RΓ(F U', K)
⊗^L_{O(F U')} O'(U')` and whose field `sectionsIso_restrictionMap` says that this computation is
compatible with the canonical derived restriction maps. That computation is a *hypothesis* here,
not a theorem: it is the commutation of derived pullback with localization, which the ambient
library does not have for these presheaf-level derived categories. For that reason the
declarations below carry no Stacks attribute, even though `isQC_Lpullback` is the conclusion of
Lemma 21.43.3: what is proved is the implication from that computation to the preservation of the
cartesian condition, which is weaker than the lemma itself. The compatibility is stated for the
canonical derived *restriction* maps rather than for the comparison maps whose invertibility is
at issue, so that nothing in the hypothesis presupposes the conclusion.

What is proved outright is the descent of a commuting square of restrictions of scalars to
derived categories, and the resulting agreement of the two ways round the base-change square:
the two composites of derived base changes are left adjoints of the two composites of derived
restrictions of scalars, so an isomorphism of the latter conjugates to an isomorphism of the
former. The comparison map of `Lg^*K` is then computed by transposing through the base-change
adjunction, the transposition being governed by the mate of the inverse base-change square.

UNIVERSES. The module universe is `max u v u' v' r`, the smallest one containing both site
universes and the ring universe: derived sections on the two sides take values in derived
categories of modules over `O(F U')` and over `O'(U')`, which the base change along the structure
map relates, so a single module universe has to serve both. This is why `DMod` appears as
`DMod.{max u' v'} O` and as `DMod.{max u v} O'`: those two annotations name the same module
universe, since `DMod.{w}` places its modules in `max u v r w`. The two site universes and the
ring universe remain independent.

## References

* [Stacks Project, Lemma 21.43.3 (Tag 0GZ1)](https://stacks.math.columbia.edu/tag/0GZ1)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons
  (mapDerivedCategoryCompIso mapDerivedCategoryIsoOfNatIso)

universe r v u v' u'

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

attribute [local instance] HasDerivedCategory.standard

section RestrictScalars

universe t

/-- Restriction of scalars along a ring homomorphism preserves finite limits: it is the identity
on underlying abelian groups, and limits of modules are computed there. -/
instance restrictScalarsPreservesFiniteLimits {R S : RingCat.{r}} (ψ : R ⟶ S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{t} ψ.hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Restriction of scalars along a ring homomorphism preserves finite colimits: it is the
identity on underlying abelian groups, and colimits of modules are computed there. -/
instance restrictScalarsPreservesFiniteColimits {R S : RingCat.{r}} (ψ : R ⟶ S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{t} ψ.hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Derived restriction of scalars `D(S) ⥤ D(R)` along a ring homomorphism `ψ : R ⟶ S`. It is the
descent of restriction of scalars, which is exact, so no derived correction is needed. -/
abbrev dRestrictScalars {R S : RingCat.{r}} (ψ : R ⟶ S) :
    DerivedCategory (ModuleCat.{t} S) ⥤ DerivedCategory (ModuleCat.{t} R) :=
  (ModuleCat.restrictScalars.{t} ψ.hom).mapDerivedCategory

/-- A commuting square of ring homomorphisms induces a commuting square of derived restrictions
of scalars: both composites are derived restriction of scalars along the common diagonal. -/
def dRestrictScalarsSquare {R₁ R₂ S₁ S₂ : RingCat.{r}} (α : R₁ ⟶ R₂) (β : R₂ ⟶ S₂)
    (γ : R₁ ⟶ S₁) (δ : S₁ ⟶ S₂) (h : γ ≫ δ = α ≫ β) :
    dRestrictScalars.{r, t} δ ⋙ dRestrictScalars.{r, t} γ ≅
      dRestrictScalars.{r, t} β ⋙ dRestrictScalars.{r, t} α :=
  (mapDerivedCategoryCompIso (ModuleCat.restrictScalars.{t} δ.hom)
      (ModuleCat.restrictScalars.{t} γ.hom)).symm ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _
      (ModuleCat.restrictScalarsComp'.{t} γ.hom δ.hom (γ ≫ δ).hom rfl)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _
      (ModuleCat.restrictScalarsComp'.{t} α.hom β.hom (γ ≫ δ).hom (by rw [h]; rfl)) ≪≫
    mapDerivedCategoryCompIso (ModuleCat.restrictScalars.{t} β.hom)
      (ModuleCat.restrictScalars.{t} α.hom)

end RestrictScalars

section Transpose

variable {A : Type*} [Category A] {B : Type*} [Category B] {A' : Type*} [Category A']
  {B' : Type*} [Category B'] {G : A ⥤ A'} {H : B ⥤ B'} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : A' ⥤ B'} {R₂ : B' ⥤ A'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Adjoint transpose of a composite through a square of adjunctions. If `β` is a mate of `α`,
as witnessed by the unit identity `hβ`, then the transpose of `L₂ s ≫ α ≫ H c ≫ e` is obtained
from the transpose of `c` by applying `G` and composing with `β` and with `R₂ e`. -/
theorem homEquiv_comp_of_unit_eq (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : ∀ Y : A, G.map (adj₁.unit.app Y) ≫ β.app (L₁.obj Y) =
      adj₂.unit.app (G.obj Y) ≫ R₂.map (α.app Y))
    {Y : A} {Z : B} (c : L₁.obj Y ⟶ Z) {W : A'} (s : W ⟶ G.obj Y) {T : B'}
    (e : H.obj Z ⟶ T) :
    adj₂.homEquiv W T (L₂.map s ≫ α.app Y ≫ H.map c ≫ e) =
      s ≫ G.map (adj₁.homEquiv Y Z c) ≫ β.app Z ≫ R₂.map e := by
  have h₁ := hβ Y
  have h₂ := β.naturality c
  simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₁]

end Transpose

section Setting

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')

/-- Derived restriction of scalars along the structure map `O(F U') ⟶ O'(U')` of the morphism of
ringed topoi. -/
abbrev dStructure (U' : C'ᵒᵖ) :
    DerivedCategory (ModuleCat.{max u v u' v' r} (O'.obj U')) ⥤
      DerivedCategory (ModuleCat.{max u v u' v' r} (O.obj (F.op.obj U'))) :=
  dRestrictScalars (φ.app U')

/-- The square of derived restrictions of scalars attached to a morphism `a' : V' ⟶ U'` of
`C'ᵒᵖ`: restricting along `O'(V') ⟶ O'(U')` and then along the structure map at `V'` agrees with
restricting along the structure map at `U'` and then along `O(F V') ⟶ O(F U')`, the underlying
square of rings commuting by naturality of the structure map. -/
def structureSquare {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    DRestrict.{max u v} O' a' ⋙ dStructure F O O' φ V' ≅
      dStructure F O O' φ U' ⋙ DRestrict.{max u' v'} O (F.op.map a') :=
  dRestrictScalarsSquare (O.map (F.op.map a')) (φ.app U') (φ.app V') (O'.map a')
    (φ.naturality a').symm

/-- **Derived base change along the structure maps.** For each object `U'` of `C'` the derived
base change `- ⊗^L_{O(F U')} O'(U')`, characterized as the left adjoint of derived restriction of
scalars along the structure map. A left adjoint is unique up to unique natural isomorphism, so
this datum is determined by the morphism of ringed topoi. -/
structure StructureBaseChange where
  /-- Derived base change `- ⊗^L_{O(F U')} O'(U')`. -/
  baseChange : ∀ U' : C'ᵒᵖ,
    DerivedCategory (ModuleCat.{max u v u' v' r} (O.obj (F.op.obj U'))) ⥤
      DerivedCategory (ModuleCat.{max u v u' v' r} (O'.obj U'))
  /-- The base change is the left adjoint of derived restriction of scalars along the structure
  map, which pins it down up to unique natural isomorphism. -/
  adj : ∀ U' : C'ᵒᵖ, baseChange U' ⊣ dStructure F O O' φ U'

variable {F O O' φ}

/-- The base-change square of the morphism of ringed topoi: base change along `O(F V') ⟶ O(F U')`
followed by base change along the structure map at `U'` agrees with base change along the
structure map at `V'` followed by base change along `O'(V') ⟶ O'(U')`. The two sides are left
adjoints of the two sides of `structureSquare`, so this is its conjugate. -/
def baseChangeSquare (sbc : StructureBaseChange F O O' φ)
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    bc.baseChange (F.op.map a') ⋙ sbc.baseChange U' ≅
      sbc.baseChange V' ⋙ bc'.baseChange a' :=
  (conjugateIsoEquiv ((sbc.adj V').comp (bc'.baseChangeAdj a'))
    ((bc.baseChangeAdj (F.op.map a')).comp (sbc.adj U'))).symm (structureSquare F O O' φ a')

/-- The canonical comparison attached to `a' : V' ⟶ U'` from the base change at `V'` of a derived
restriction of scalars to the derived restriction of scalars of a base change at `U'`: the mate
of the inverse base-change square under the two base-change adjunctions. -/
def restrictionMate (sbc : StructureBaseChange F O O' φ)
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    DRestrict.{max u' v'} O (F.op.map a') ⋙ sbc.baseChange V' ⟶
      sbc.baseChange U' ⋙ DRestrict.{max u v} O' a' :=
  mateEquiv (bc.baseChangeAdj (F.op.map a')) (bc'.baseChangeAdj a')
    (baseChangeSquare sbc bc bc' a').inv

/-- The unit identity that characterizes `restrictionMate` as a mate of the inverse base-change
square. -/
theorem unit_restrictionMate (sbc : StructureBaseChange F O O' φ)
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (Y : DerivedCategory (ModuleCat.{max u v u' v' r} (O.obj (F.op.obj V')))) :
    (sbc.baseChange V').map ((bc.baseChangeAdj (F.op.map a')).unit.app Y) ≫
        (restrictionMate sbc bc bc' a').app ((bc.baseChange (F.op.map a')).obj Y) =
      (bc'.baseChangeAdj a').unit.app ((sbc.baseChange V').obj Y) ≫
        (DRestrict.{max u v} O' a').map ((baseChangeSquare sbc bc bc' a').inv.app Y) :=
  unit_mateEquiv _ _ _ Y

/-- **The mate of `restrictionMate` is the square of derived restrictions of scalars.** Taking
mates a second time, now along the two base-change adjunctions of the structure maps, returns
`structureSquare`: the base-change square is the conjugate of that square, and the twice-iterated
mate of a two-cell whose four functors are left adjoints is its conjugate. So `restrictionMate`
is determined by the commuting square of rings alone, with no choice of base change entering. -/
theorem mate_restrictionMate (sbc : StructureBaseChange F O O' φ)
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O')
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    (mateEquiv (sbc.adj U') (sbc.adj V')
        (restrictionMate sbc bc bc' a')).natTrans =
      (structureSquare F O O' φ a').inv :=
  (iterated_mateEquiv_conjugateEquiv (bc.baseChangeAdj (F.op.map a'))
      (bc'.baseChangeAdj a') (sbc.adj V') (sbc.adj U')
      (baseChangeSquare sbc bc bc' a').inv).trans
    (Equiv.apply_symm_apply _ _)

/-- **The derived pullback of a morphism of ringed topoi, with its derived sections.** The
functor `Lg^* : D(O) ⥤ D(O')`, together with the computation of its derived sections over an
object `U'` of `C'` as the derived sections of the argument over `F U'`, base changed along the
structure map, and the compatibility of that computation with the canonical derived restriction
maps. -/
structure DerivedPullbackData (sbc : StructureBaseChange F O O' φ)
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O') where
  /-- The derived pullback `Lg^* : D(O) ⥤ D(O')`. -/
  Lpullback : DMod.{max u' v'} O ⥤ DMod.{max u v} O'
  /-- `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^L_{O(F U')} O'(U')`, naturally in `K`. -/
  sectionsIso : ∀ U' : C'ᵒᵖ,
    Lpullback ⋙ RGamma.{max u v} O' U' ≅
      RGamma.{max u' v'} O (F.op.obj U') ⋙ sbc.baseChange U'
  /-- `sectionsIso` carries the canonical derived restriction maps of `Lg^*K` to the canonical
  derived restriction maps of `K`, transported along `restrictionMate`. -/
  sectionsIso_restrictionMap : ∀ {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : DMod.{max u' v'} O),
    restrictionMap.{max u v} O' a' (Lpullback.obj K) ≫
        (DRestrict.{max u v} O' a').map ((sectionsIso U').hom.app K) =
      (sectionsIso V').hom.app K ≫
        (sbc.baseChange V').map (restrictionMap.{max u' v'} O (F.op.map a') K) ≫
        (restrictionMate sbc bc bc' a').app ((RGamma.{max u' v'} O (F.op.obj U')).obj K)

variable {sbc : StructureBaseChange F O O' φ} {bc : BaseChangeData.{max u' v'} O}
  {bc' : BaseChangeData.{max u v} O'}

/-- The canonical comparison map of `Lg^*K` factors through the canonical comparison map of `K`:
it is the base change along the structure map at `U'` of the comparison map of `K` along `F a'`,
conjugated by the base-change square and by the computation of the derived sections of
`Lg^*K`. -/
theorem comparison_Lpullback (d : DerivedPullbackData sbc bc bc') {U' V' : C'ᵒᵖ}
    (a' : V' ⟶ U') (K : DMod.{max u' v'} O) :
    comparison.{max u v} bc' a' (d.Lpullback.obj K) =
      (bc'.baseChange a').map ((d.sectionsIso V').hom.app K) ≫
        (baseChangeSquare sbc bc bc' a').inv.app
          ((RGamma.{max u' v'} O (F.op.obj V')).obj K) ≫
        (sbc.baseChange U').map (comparison.{max u' v'} bc (F.op.map a') K) ≫
        (d.sectionsIso U').inv.app K := by
  have hc := d.sectionsIso_restrictionMap a' K
  rw [← Category.assoc] at hc
  have key := homEquiv_comp_of_unit_eq (bc.baseChangeAdj (F.op.map a')) (bc'.baseChangeAdj a')
    (baseChangeSquare sbc bc bc' a').inv (restrictionMate sbc bc bc' a')
    (unit_restrictionMate sbc bc bc' a') (comparison.{max u' v'} bc (F.op.map a') K)
    ((d.sectionsIso V').hom.app K) ((d.sectionsIso U').inv.app K)
  simp only [Functor.comp_obj] at key
  apply ((bc'.baseChangeAdj a').homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, key, Equiv.apply_symm_apply, ← Category.assoc,
    ← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- **Derived pullback carries cartesian objects to cartesian objects.** If the derived sections
of `K` are cartesian, then so are the derived sections of `Lg^*K`: the comparison map of `Lg^*K`
along a morphism `a'` of `C'ᵒᵖ` is the base change of the comparison map of `K` along `F a'`,
conjugated by isomorphisms. -/
theorem isQC_Lpullback (d : DerivedPullbackData sbc bc bc') (K : DMod.{max u' v'} O)
    (hK : IsQC.{max u' v'} bc K) : IsQC.{max u v} bc' (d.Lpullback.obj K) := by
  intro U' V' a'
  rw [comparison_Lpullback d a' K]
  have := hK (F.op.map a')
  infer_instance

/-- The functor `QC(O) ⥤ QC(O')` through which the derived pullback factors, the full
subcategories of objects with cartesian derived sections being stable under `Lg^*`. -/
def qcPullback (d : DerivedPullbackData sbc bc bc') :
    QC.{max u' v'} bc ⥤ QC.{max u v} bc' :=
  ObjectProperty.lift _ (QCι.{max u' v'} bc ⋙ d.Lpullback)
    (fun K => isQC_Lpullback d K.obj K.property)

end Setting

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
