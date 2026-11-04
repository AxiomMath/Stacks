module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPresentation
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionNaiveExt

/-!
# The class of a square-zero extension through an arbitrary presentation (Stacks 0GQ6)

Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi, `𝒢` an `𝒪`-module and
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` an extension of `f⁻¹𝒪_ℬ`-algebras with `𝒢` an ideal of square zero.
**Stacks 0GQ6** chooses a sheaf of sets `ℰ` with a commutative diagram `α' : ℰ ⟶ 𝒪'`,
`α : ℰ ⟶ 𝒪` over the reduction `𝒪' ⟶ 𝒪` such that `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective with kernel
`𝒥`. Then `NL_{𝒪/𝒪_ℬ} ≅ NL(α)` by **Stacks 08TY**, `α'` determines a map
`f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪'`, hence a map `𝒥/𝒥² ⟶ 𝒢`, and its class in
`Ext¹_𝒪(NL(α), 𝒢) = Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` is the element corresponding to `𝒪'` under the
bijection of **Stacks 0GQ5**.

## Main definitions

* `CompatibleFirstOrderThickening.generatorsLift`: the map `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪'` determined by
  `α'`, for an arbitrary sheaf of sets `ℰ`; for `ℰ` the sheaf of sets underlying `𝒪'` and `α'`
  the identity it is `CompatibleFirstOrderThickening.lift`.
* `CompatibleFirstOrderThickening.generatorsIdealRestriction` and
  `CompatibleFirstOrderThickening.generatorsConormalToIdeal`: the map `𝒥/𝒥² ⟶ 𝒢` it
  determines, `h ↦ α'(h)` read in the square-zero ideal and carried to `𝒢`.
* `RingedToposExtensionProblem.generatorsPairDatum`: `(ℰ, α)` as a family of generators for the
  pair of solutions `(𝒪 ⊕ 𝒢, 𝒪')`, lifted by the zero section and by `α'`.

## Main results

* `RingedToposExtensionProblem.isLocallySurjective_presentation_of_isLocallySurjective` and
  `RingedToposExtensionProblem.exists_generators_ofTrivialBase`: the choice of `(ℰ, α, α')` is
  possible, for instance with any sheaf of sets surjecting onto `𝒪'`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_comp`: composing the algebra map classifying
  `(a, e)` with `g` classifies `(a ≫ g, e ≫ g)`.
* `Stacks.SheafOfModules.isIso_Q_map_naiveCotangentComplexComparison`: the comparison
  `NL(α) ⟶ NL_{B/A}` is an isomorphism in the derived category, by [Stacks 08TY].
* `RingedToposExtensionProblem.generatorsPairDatum_conormalMap`: the difference map of that pair
  datum is the map `𝒥/𝒥² ⟶ 𝒢` of `α'`.
* `RingedToposExtensionProblem.squareZeroExtensionClassesEquiv_mk_eq_generators`:
  **Stacks 0GQ6.** For every `(ℰ, α, α')` as above, the class of `𝒥/𝒥² ⟶ 𝒢` in
  `Ext¹_𝒪(NL(α), 𝒢)`, transported along the isomorphism `NL(α) ≅ NL_{𝒪/𝒪_ℬ}` of
  [Stacks 08TY], is the image of the class of `𝒪'` under the bijection of [Stacks 0GQ5].

## References

* [Stacks Project, Tag 0GQ6](https://stacks.math.columbia.edu/tag/0GQ6)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.Differentials (sqZeroExtSheafInl)
open Stacks.Sites.Conormal (IdealRestriction conormalDesc kernelIdeal kernelIdeal_le_comap
  hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  baseChange)

universe t u v' u' w'

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

/-! ### Composing a map out of a free algebra sheaf -/

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v'} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w'}]

/-- The algebra map `A[ℰ] ⟶ T` classifying `(a, e)`, followed by `g : T ⟶ T'`, classifies
`(a ≫ g, e ≫ g)`. -/
theorem freeAlgebraSheafDesc_comp (A T T' : Sheaf J CommRingCat.{w'})
    (E : Functor Cᵒᵖ (Type w')) (a : A ⟶ T) (e : E ⟶ underlyingPresheaf J T) (g : T ⟶ T') :
    freeAlgebraSheafDesc J A T E a e ≫ g =
      freeAlgebraSheafDesc J A T' E (a ≫ g)
        (e ≫ Functor.whiskerRight g.hom (forget CommRingCat.{w'})) := by
  refine freeAlgebraSheaf_hom_ext J A T' E ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_desc,
      freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc, freeAlgebraSheafVariable_comp_desc]
    rfl

end Stacks.Sites.FreeAlgebra

/-! ### The comparison `NL(α) ⟶ NL_{B/A}` in the derived category -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v'} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w'}] [J.WEqualsLocallyBijective CommRingCat.{w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (A B : Sheaf J CommRingCat.{w'}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w'))
  (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w' u v' u'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w' u v' u'}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max w' u v' u'}
    (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- **Stacks 08TY** in the derived category: the canonical comparison `NL(α) ⟶ NL_{B/A}` of a
polynomial presentation becomes an isomorphism in `D(B)`. -/
instance isIso_Q_map_naiveCotangentComplexComparison :
    IsIso (DerivedCategory.Q.map (naiveCotangentComplexComparison.{v', u, w', u'} J A B a E α)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_naiveCotangentComplexComparison_site.{v', u, w', u'} J A B a E α)

end Stacks.SheafOfModules

namespace Deformation.ToposThickening.RingedToposExtensionProblem

/-! ### The map `𝒥/𝒥² ⟶ 𝒢` attached to an arbitrary presentation -/

namespace CompatibleFirstOrderThickening

section Generators

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B} (P : S.CompatibleFirstOrderThickening)
  [HasWeakSheafify X.J CommRingCat.{u}]
  {A : Sheaf X.J CommRingCat.{u}} (a : A ⟶ X.O)
  (E : Functor X.Cᵒᵖ (Type u)) (α : E ⟶ underlyingPresheaf X.J X.O)
  (α' : E ⟶ underlyingPresheaf X.J P.extension)
  (base : A ⟶ P.extension)

/-- The map `A[ℰ] ⟶ 𝒪'` of `A`-algebras determined by `α' : ℰ ⟶ 𝒪'`, for an algebra structure
`base : A ⟶ 𝒪'`; in the source `A = f⁻¹𝒪_ℬ`. -/
abbrev generatorsLift : freeAlgebraSheaf X.J A E ⟶ P.extension :=
  freeAlgebraSheafDesc X.J A P.extension E base α'

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- For `ℰ` the sheaf of sets underlying `𝒪'` and `α'` the identity, `generatorsLift` is the map
`CompatibleFirstOrderThickening.lift` of the canonical presentation. -/
theorem lift_eq_generatorsLift [HasWeakSheafify X.J CommRingCat.{u}]
    (base : inverseImageBaseRing S ⟶ P.extension) :
    P.lift base = P.generatorsLift P.generators (𝟙 _) base :=
  Stacks.Sites.FreeAlgebra.canonicalPresentation_eq_desc X.J _ _ base

variable {a E α α' base}
  (hα : α' ≫ Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u}) = α)
  (hbase : base ≫ P.reduction = a)

include hα hbase in
/-- The commutative diagram of the source: the map `A[ℰ] ⟶ 𝒪'` determined by `α'`, followed by
the reduction `𝒪' ⟶ 𝒪`, is the presentation attached to `α`. -/
theorem generatorsLift_comp_reduction :
    P.generatorsLift E α' base ≫ P.reduction =
      Stacks.SheafOfModules.presentation X.J A X.O a E α := by
  rw [Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_comp, hbase, hα]

include hα hbase in
/-- A local relation of the presentation `A[ℰ] ⟶ 𝒪` is carried by `α'` into the square-zero
ideal. -/
theorem generatorsLift_mem_kernelIdeal (U : X.Cᵒᵖ)
    (h : kernelIdeal (Stacks.SheafOfModules.presentation X.J A X.O a E α).hom U) :
    ((P.generatorsLift E α' base).hom.app U).hom h.1 ∈ kernelIdeal P.reduction.hom U :=
  kernelIdeal_le_comap _ P.reduction.hom (P.generatorsLift E α' base).hom
    (hom_of_comp_eq (P.generatorsLift_comp_reduction hα hbase)) U h.2

/-- The map `𝒥(U) ⟶ 𝒢(U)` on sections determined by `α'`: apply the map `A[ℰ] ⟶ 𝒪'`, then
read the result in the square-zero ideal, identified with `𝒢`. -/
def generatorsIdealRestriction :
    IdealRestriction.{u, u, u, u} (Stacks.SheafOfModules.presentation X.J A X.O a E α) S.G where
  app U :=
    { toFun := fun h ↦ P.kernelIdentification.app U
        ⟨((P.generatorsLift E α' base).hom.app U).hom h.1,
          P.generatorsLift_mem_kernelIdeal hα hbase U h⟩
      map_zero' :=
        Eq.trans
          (congrArg (P.kernelIdentification.app U)
            (Subtype.ext (map_zero ((P.generatorsLift E α' base).hom.app U).hom)))
          (map_zero (P.kernelIdentification.app U))
      map_add' := fun h h' ↦
        Eq.trans
          (congrArg (P.kernelIdentification.app U)
            (Subtype.ext (map_add ((P.generatorsLift E α' base).hom.app U).hom _ _)))
          (map_add (P.kernelIdentification.app U) _ _) }
  app_smul U r h :=
    Eq.trans
      (congrArg (P.kernelIdentification.app U)
        (Subtype.ext (map_mul ((P.generatorsLift E α' base).hom.app U).hom r h.1)))
      (Eq.trans (P.kernelIdentification.app_smul U
          (((P.generatorsLift E α' base).hom.app U).hom r) _)
        (congrArg
          (· • P.kernelIdentification.app U
            ⟨((P.generatorsLift E α' base).hom.app U).hom h.1,
              P.generatorsLift_mem_kernelIdeal hα hbase U h⟩)
          (congrArg (fun t : _ ⟶ X.O ↦ (t.hom.app U).hom r)
            (P.generatorsLift_comp_reduction hα hbase))))
  app_map {U V} i h := by
    refine Eq.trans ?_
      (P.kernelIdentification.app_map i
        ⟨((P.generatorsLift E α' base).hom.app U).hom h.1,
          P.generatorsLift_mem_kernelIdeal hα hbase U h⟩)
    refine congrArg (P.kernelIdentification.app V) (Subtype.ext ?_)
    exact NatTrans.naturality_apply (P.generatorsLift E α' base).hom i h.1

/-- On a local relation `h` of the presentation the restriction datum is `α'(h)`, read in the
square-zero ideal and carried to `𝒢`. -/
theorem generatorsIdealRestriction_app (U : X.Cᵒᵖ)
    (h : kernelIdeal (Stacks.SheafOfModules.presentation X.J A X.O a E α).hom U) :
    (P.generatorsIdealRestriction hα hbase).app U h =
      P.kernelIdentification.app U
        ⟨((P.generatorsLift E α' base).hom.app U).hom h.1,
          P.generatorsLift_mem_kernelIdeal hα hbase U h⟩ :=
  rfl

variable [Presheaf.IsLocallySurjective X.J
  (Stacks.SheafOfModules.presentation X.J A X.O a E α).hom]

/-- The map `𝒥/𝒥² ⟶ 𝒢` determined by `α'`, for an arbitrary sheaf of sets `ℰ` with
`α' : ℰ ⟶ 𝒪'` over `α : ℰ ⟶ 𝒪` and `A[ℰ] ⟶ 𝒪` surjective with kernel `𝒥`. -/
abbrev generatorsConormalToIdeal :
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u} X.J A X.O a E α).X₁ ⟶
      S.G :=
  conormalDesc.{u, u, u, u} _ S.G (P.generatorsIdealRestriction hα hbase)

end Generators

/-! ### The zero section of the trivial extension on a family of generators -/

section TrivialSolution

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B} (h : IsIso S.baseReduction)
  {Q : S.CompatibleFirstOrderThickening}

/-- For a pair datum whose first family is `α` followed by the zero section of the trivial
extension `𝒪 ⊕ 𝒢`, the first lift `f⁻¹𝒪_{ℬ'}[ℰ] ⟶ 𝒪 ⊕ 𝒢` is the presentation followed by the
zero section; in particular it kills the kernel of the presentation. -/
theorem PairDatum.lift₁_eq_of_trivialSolution (d : PairDatum (S.trivialSolution h) Q)
    (hβ : d.β₁ = d.α ≫ Functor.whiskerRight (sqZeroExtSheafInl X.O S.G).hom
      (forget CommRingCat.{u})) :
    d.lift₁ = d.restrictedPresentation ≫ sqZeroExtSheafInl X.O S.G := by
  rw [Category.assoc, Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_comp,
    Stacks.Sites.FreeAlgebra.baseChange_comp_desc, ← hβ]
  rfl

end TrivialSolution

end CompatibleFirstOrderThickening

/-! ### Stacks 0GQ6 -/

section Remark

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {f : RingedToposHom X B}
  {G : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}

/-- The structure map `f⁻¹𝒪_ℬ ⟶ 𝒪'` of an extension of `f⁻¹𝒪_ℬ`-algebras lies over
`f^♯ : f⁻¹𝒪_ℬ ⟶ 𝒪`. -/
theorem baseMap_comp_reduction_ofTrivialBase
    (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening) :
    Q.baseMap ≫ Q.reduction = f.fSharpInverseImage :=
  Q.baseMap_reduction.trans
    ((congrArg (· ≫ f.fSharpInverseImage)
      ((inverseImageCommRingFunctor f.toToposHom).map_id B.O)).trans (Category.id_comp _))

/-- Changing the coefficients of a free algebra sheaf along the inverse image of the identity of
`𝒪_ℬ` is the identity on sections. -/
theorem baseChange_inverseImage_map_id_apply (E : Functor X.Cᵒᵖ (Type u)) (U : X.Cᵒᵖ)
    (x : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor f.toToposHom).obj B.O) E).obj.obj
      U) :
    (baseChange X.J ((inverseImageCommRingFunctor f.toToposHom).map (𝟙 B.O)) E).hom.app U x =
      x := by
  rw [CategoryTheory.Functor.map_id, Stacks.Sites.FreeAlgebra.baseChange_id]
  rfl

/-- For any sheaf of sets `ℰ` with a surjection `α' : ℰ ⟶ 𝒪'`, the presentation
`f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` of `α = α'` followed by the reduction is surjective. -/
@[stacks 0GQ6]
theorem isLocallySurjective_presentation_of_isLocallySurjective
    (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening) (E : Functor X.Cᵒᵖ (Type u))
    (α' : E ⟶ underlyingPresheaf X.J Q.extension) [Presheaf.IsLocallySurjective X.J α'] :
    Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E
        (α' ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u}))).hom := by
  have : Presheaf.IsLocallySurjective X.J
      (Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u})) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q.reduction.hom).mp
      Q.locallySurjective
  have := Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O E f.fSharpInverseImage
      (α' ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u})))
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr (by assumption)

/-- For every extension `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_ℬ`-algebras there are a sheaf of sets
`ℰ` and maps `α' : ℰ ⟶ 𝒪'`, `α : ℰ ⟶ 𝒪` forming a commutative triangle over `𝒪' ⟶ 𝒪` for which
`f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective; for instance `ℰ` the sheaf of sets underlying `𝒪'` and `α'` the
identity. -/
@[stacks 0GQ6]
theorem exists_generators_ofTrivialBase
    (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening) :
    ∃ (E : Functor X.Cᵒᵖ (Type u)) (α' : E ⟶ underlyingPresheaf X.J Q.extension)
      (α : E ⟶ underlyingPresheaf X.J X.O),
      α' ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u}) = α ∧
        Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E α).hom :=
  ⟨underlyingPresheaf X.J Q.extension, 𝟙 _, _, rfl,
    isLocallySurjective_presentation_of_isLocallySurjective Q _ (𝟙 _)⟩

variable (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening)
  (E : Functor X.Cᵒᵖ (Type u)) (α : E ⟶ underlyingPresheaf X.J X.O)
  (α' : E ⟶ underlyingPresheaf X.J Q.extension)
  (hα : α' ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{u}) = α)
  [Presheaf.IsLocallySurjective X.J (Stacks.SheafOfModules.presentation X.J
    ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E α).hom]

/-- The family of generators `(ℰ, α)` for the pair of solutions `(𝒪 ⊕ 𝒢, 𝒪')`: it lifts to the
trivial extension by the zero section and to `𝒪'` by `α'`. -/
def generatorsPairDatum :
    CompatibleFirstOrderThickening.PairDatum
      ((ofTrivialBase f G).trivialSolution (IsIso.id B.O)) Q where
  E := E
  α := α
  β₁ := α ≫ Functor.whiskerRight (sqZeroExtSheafInl X.O G).hom (forget CommRingCat.{u})
  β₂ := α'
  comm₁ := rfl
  comm₂ := hα
  isLocallySurjective := ‹_›

/-- **The difference map of the pair datum `(𝒪 ⊕ 𝒢, 𝒪')` on `(ℰ, α, α')` is the map
`𝒥/𝒥² ⟶ 𝒢` of `α'`.** -/
theorem generatorsPairDatum_conormalMap :
    (generatorsPairDatum Q E α α' hα).conormalMap =
      Q.generatorsConormalToIdeal (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O)
          (a := f.fSharpInverseImage) (base := Q.baseMap) hα
        (baseMap_comp_reduction_ofTrivialBase Q) := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  refine (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x).trans
    (Eq.trans ?_ (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x).symm)
  have hψ := baseChange_inverseImage_map_id_apply (f := f) E U x.1
  let k : kernelIdeal (generatorsPairDatum Q E α α' hα).restrictedPresentation.hom U :=
    ⟨x.1, (congrArg ((Stacks.SheafOfModules.presentation X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E
        α).hom.app U) hψ).trans x.2⟩
  have hk : (baseChange X.J ((inverseImageCommRingFunctor f.toToposHom).map (𝟙 B.O))
      E).hom.app U x.1 ∈ kernelIdeal (generatorsPairDatum Q E α α' hα).presentation.hom U :=
    hψ.symm ▸ x.2
  have hx : x = ⟨_, hk⟩ := Subtype.ext hψ.symm
  rw [hx]
  refine (Stacks.Sites.Conormal.IdealRestriction.descend_app_mk
    (generatorsPairDatum Q E α α' hα).difference _ k hk).trans ?_
  refine ((generatorsPairDatum Q E α α' hα).difference_app_eq k 0 _ ?_ ?_).trans (sub_zero _)
  · refine ((ofTrivialBase f G).trivialSolution (IsIso.id B.O)).incl_zero.trans ?_
    refine Eq.trans ?_ (congrArg (fun φ ↦ (φ.hom.app U).hom k.1)
      (CompatibleFirstOrderThickening.PairDatum.lift₁_eq_of_trivialSolution
        (S := ofTrivialBase f G) (IsIso.id B.O) (generatorsPairDatum Q E α α' hα) rfl)).symm
    exact ((congrArg (fun y ↦ ((sqZeroExtSheafInl X.O G).hom.app U).hom y) k.2).trans
      (map_zero _)).symm
  · exact (Q.incl_kernelPreimage _).trans
      (congrArg ((Q.generatorsLift E α' Q.baseMap).hom.app U) hψ)

/-- Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi, `𝒢` an `𝒪`-module and
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` an extension of `f⁻¹𝒪_ℬ`-algebras with `𝒢` an ideal of square zero. Let
`ℰ` be a sheaf of sets with a commutative diagram `α' : ℰ ⟶ 𝒪'`, `α : ℰ ⟶ 𝒪` over `𝒪' ⟶ 𝒪` such
that `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective with kernel `𝒥`. The map `𝒥/𝒥² ⟶ 𝒢` determined by `α'` has a
class in `Ext¹_𝒪(NL(α), 𝒢)`; transported along the isomorphism `NL(α) ≅ NL_{𝒪/𝒪_ℬ}` of
[Stacks 08TY], it is the element of `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` corresponding to `𝒪'` under the
bijection of [Stacks 0GQ5]. -/
@[stacks 0GQ6]
theorem squareZeroExtensionClassesEquiv_mk_eq_generators
    [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)] :
    inv (DerivedCategory.Q.map
        (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E α)) ≫
      Stacks.SheafOfModules.presentationConormalExtClass.{u, u, u, t} X.J
        ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage E α G
        (Q.generatorsConormalToIdeal (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O)
          (a := f.fSharpInverseImage) (base := Q.baseMap) hα
        (baseMap_comp_reduction_ofTrivialBase Q)) =
      squareZeroExtensionClassesEquiv f G
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) Q) := by
  rw [squareZeroExtensionClassesEquiv_mk,
    ← (generatorsPairDatum Q E α α' hα).obstruction_eq_pairObstruction,
    CompatibleFirstOrderThickening.PairDatum.obstruction,
    CompatibleFirstOrderThickening.PairDatum.extClass, generatorsPairDatum_conormalMap]
  rfl

end Remark

end Deformation.ToposThickening.RingedToposExtensionProblem

end
