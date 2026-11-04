module
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.MonCat.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute
/-!
# Stacks 007N: A list of categories of algebraic structures

The Stacks Project asserts at tag 007N that the following seven categories,
each equipped with the obvious forgetful functor to `Type`, are types of
algebraic structures (Stacks 007L):

1. pointed sets,
2. abelian groups,
3. groups,
4. monoids,
5. (commutative) rings,
6. modules over a fixed commutative ring,
7. Lie algebras over a fixed field.

The Stacks proof is "Omitted." We give the construction for each item. For the
categories already well-developed in Mathlib (`AddCommGrpCat`, `MonCat`,
`CommRingCat`, `ModuleCat`) the four required properties are direct typeclass
synthesis. For `GrpCat` we register the missing `HasFilteredColimits` instance
using Mathlib's existing filtered-colimit cocone. For `Pointed` we build the
limit cone and filtered colimit cocone explicitly, lifting from `Type`. For Lie
algebras over a field `K` we introduce the bundled category `LieAlgCat K`
(Mathlib has no such category at present) and construct limits and filtered
colimits by lifting through the underlying `ModuleCat K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

/-! ## The 007L predicate -/

/-- A pair `(C, F)` of a category `C` together with a functor `F : C ⥤ Type v` is a
**type of algebraic structures** (Stacks 007L) when:
* `F` is faithful;
* `C` has all (small) limits and `F` preserves them;
* `C` has all (small) filtered colimits and `F` preserves them;
* `F` reflects isomorphisms.

This is the predicate (`Prop`-valued) form of the 007L definition. The bundled form is
`AlgebraicStructureType`, in `StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs`, which is
the declaration carrying the 007M tag; `toAlgebraicStructureType` and
`AlgebraicStructureType.isTypeOfAlgebraicStructure` below move between the two, so a theorem
stated for the bundle can be applied to any of the seven examples in this file. -/
structure IsTypeOfAlgebraicStructure (C : Type u) [Category.{v} C]
    (F : C ⥤ Type v) : Prop where
  /-- The forgetful functor `F` is faithful. -/
  faithful : F.Faithful
  /-- The category `C` has all (small) limits. -/
  hasLimits : HasLimitsOfSize.{v, v} C
  /-- The forgetful functor `F` preserves all (small) limits. -/
  preservesLimits : PreservesLimitsOfSize.{v, v} F
  /-- The category `C` has all (small) filtered colimits. -/
  hasFilteredColimits : HasFilteredColimitsOfSize.{v, v} C
  /-- The forgetful functor `F` preserves all filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimits F
  /-- The forgetful functor `F` reflects isomorphisms. -/
  reflectsIsomorphisms : F.ReflectsIsomorphisms

/-! ## (1) Pointed sets

Mathlib has the adjunction `typeToPointed ⊣ forget Pointed`. This makes
`forget Pointed` a right adjoint, hence preserves all limits automatically. We
still need to give `Pointed` itself limits and filtered colimits, plus prove
that the forgetful functor preserves filtered colimits and reflects
isomorphisms. -/

namespace Pointed_

/-- The forgetful functor `forget Pointed` is a right adjoint via Mathlib's
`typeToPointedForgetAdjunction`. -/
instance forget_isRightAdjoint : (forget Pointed.{w}).IsRightAdjoint :=
  ⟨_, ⟨typeToPointedForgetAdjunction⟩⟩

/-- The forgetful functor reflects isomorphisms: a pointed morphism whose
underlying function is bijective has a set-theoretic inverse, which sends the
basepoint to the basepoint because the original morphism does. -/
instance forget_reflectsIsomorphisms :
    (forget Pointed.{w}).ReflectsIsomorphisms := by
  refine ⟨fun {X Y} f hf => ?_⟩
  rw [CategoryTheory.isIso_iff_bijective] at hf
  have hg : Function.Bijective f.toFun := hf
  let e : X.X ≃ Y.X := Equiv.ofBijective f.toFun hg
  have hsymm_point : e.symm Y.point = X.point :=
    hg.injective <| (Equiv.ofBijective_apply_symm_apply _ hg _).trans f.map_point.symm
  let finv : Y ⟶ X := ⟨e.symm, hsymm_point⟩
  exact ⟨⟨finv, Pointed.Hom.ext (funext e.symm_apply_apply),
    Pointed.Hom.ext (funext e.apply_symm_apply)⟩⟩

/-- Explicit limit cone in `Pointed.{w}` over `F : J ⥤ Pointed.{w}`: the
underlying carrier is the Types-limit of `F ⋙ forget Pointed`, and the
basepoint is the compatible tuple of basepoints. -/
noncomputable def limitCone {J : Type w} [SmallCategory J]
    (F : J ⥤ Pointed.{w}) : Cone F where
  pt :=
    { X := (Types.limitCone (F ⋙ forget Pointed.{w})).pt
      point :=
        ⟨fun j => (F.obj j).point, fun f => (F.map f).map_point⟩ }
  π :=
    { app := fun j => { toFun := fun x => x.val j, map_point := rfl }
      naturality _ _ f := Pointed.Hom.ext (funext fun x => (x.property f).symm) }

/-- `limitCone F` is a limit cone. -/
noncomputable def limitConeIsLimit {J : Type w} [SmallCategory J]
    (F : J ⥤ Pointed.{w}) : IsLimit (limitCone F) where
  lift s :=
    { toFun := fun x =>
        ⟨fun j => (s.π.app j).toFun x, fun f => congrFun (congrArg (·.toFun) (s.w f)) x⟩
      map_point := Subtype.ext (funext fun j => (s.π.app j).map_point) }
  fac _ _ := Pointed.Hom.ext (funext fun _ => rfl)
  uniq _ _ h :=
    Pointed.Hom.ext <| funext fun x =>
      Subtype.ext <| funext fun j => congrFun (congrArg (·.toFun) (h j)) x

/-- `Pointed` has limits of every small shape, given by `limitCone`. -/
instance hasLimitsOfShape (J : Type w) [SmallCategory J] :
    HasLimitsOfShape J Pointed.{w} where
  has_limit F := ⟨_, limitConeIsLimit F⟩

/-- `Pointed` has all small limits. -/
instance hasLimits : HasLimitsOfSize.{w, w} Pointed.{w} where
  has_limits_of_shape _ _ := hasLimitsOfShape _

/-- The basepoint chosen for the filtered colimit of pointed sets: image of the
basepoint at an arbitrary index `j₀`. -/
noncomputable def filteredColimitPoint {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) :
    (F ⋙ forget Pointed.{w}).ColimitType :=
  (F ⋙ forget Pointed.{w}).ιColimitType
    (Classical.choice IsFiltered.nonempty) (F.obj _).point

/-- The proposed filtered-colimit Pointed object. -/
noncomputable abbrev filteredColimitObj {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) : Pointed.{w} :=
  { X := (F ⋙ forget Pointed.{w}).ColimitType
    point := filteredColimitPoint F }

/-- Map from `F.obj j` to the proposed colimit, packaged as a morphism in
`Pointed`. The basepoint-preservation is the key non-trivial check. -/
noncomputable def filteredColimitι {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) (j : J) :
    F.obj j ⟶ filteredColimitObj F where
  toFun x := (F ⋙ forget Pointed.{w}).ιColimitType j x
  map_point := by
    set j₀ : J := Classical.choice IsFiltered.nonempty
    let k := IsFiltered.max j₀ j
    let α : j₀ ⟶ k := IsFiltered.leftToMax j₀ j
    let β : j ⟶ k := IsFiltered.rightToMax j₀ j
    calc (F ⋙ forget Pointed.{w}).ιColimitType j (F.obj j).point
        = (F ⋙ forget Pointed.{w}).ιColimitType k
            ((F ⋙ forget Pointed.{w}).map β (F.obj j).point) :=
          ((F ⋙ forget Pointed.{w}).ιColimitType_map β (F.obj j).point).symm
      _ = (F ⋙ forget Pointed.{w}).ιColimitType k
            ((F ⋙ forget Pointed.{w}).map α (F.obj j₀).point) :=
          congrArg ((F ⋙ forget Pointed.{w}).ιColimitType k)
            ((F.map β).map_point.trans (F.map α).map_point.symm)
      _ = (F ⋙ forget Pointed.{w}).ιColimitType j₀ (F.obj j₀).point :=
          (F ⋙ forget Pointed.{w}).ιColimitType_map α (F.obj j₀).point
      _ = filteredColimitPoint F := rfl

/-- Filtered colimit cocone in `Pointed.{w}`. -/
noncomputable def filteredColimitCocone {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) : Cocone F where
  pt := filteredColimitObj F
  ι :=
    { app := filteredColimitι F
      naturality _ _ f :=
        Pointed.Hom.ext (funext fun x => (F ⋙ forget Pointed.{w}).ιColimitType_map f x) }

/-- The Types-cocone whose tip is `s.pt.X`, induced by the underlying functions
of `s.ι.app`. -/
noncomputable def descCoconeTypes {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) (s : Cocone F) :
    Functor.CoconeTypes.{w} (F ⋙ forget Pointed.{w}) where
  pt := s.pt.X
  ι := fun j x => (s.ι.app j).toFun x
  ι_naturality f := funext fun x => congrFun (congrArg (·.toFun) (s.w f)) x

/-- Descent of a `Pointed` cocone from the proposed colimit: defined as the
`descColimitType` on the underlying sets, packaged with the basepoint condition. -/
noncomputable def filteredColimitDesc {J : Type w} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ Pointed.{w}) (s : Cocone F) :
    filteredColimitObj F ⟶ s.pt where
  toFun := (F ⋙ forget Pointed.{w}).descColimitType (descCoconeTypes F s)
  map_point := by
    set j₀ : J := Classical.choice IsFiltered.nonempty
    dsimp only [filteredColimitPoint]
    rw [Functor.descColimitType_ιColimitType_apply]
    dsimp only [descCoconeTypes]
    exact (s.ι.app j₀).map_point

/-- `filteredColimitCocone F` is a colimit cocone: descent and uniqueness are inherited from
the underlying Types-colimit, joint surjectivity of the `ι`s giving uniqueness. -/
noncomputable def filteredColimitCoconeIsColimit {J : Type w}
    [SmallCategory J] [IsFiltered J] (F : J ⥤ Pointed.{w}) :
    IsColimit (filteredColimitCocone F) where
  desc := filteredColimitDesc F
  fac _ _ := Pointed.Hom.ext (funext fun _ => rfl)
  uniq s m h := Pointed.Hom.ext <| funext fun x => by
    obtain ⟨j, y, rfl⟩ := (F ⋙ forget Pointed.{w}).ιColimitType_jointly_surjective x
    exact congrFun (congrArg (·.toFun) (h j)) y

/-- `Pointed` has colimits of every small filtered shape. -/
instance hasColimitsOfShape_filtered (J : Type w) [SmallCategory J]
    [IsFiltered J] : HasColimitsOfShape J Pointed.{w} where
  has_colimit F := ⟨_, filteredColimitCoconeIsColimit F⟩

/-- `Pointed` has all small filtered colimits. -/
instance hasFilteredColimits : HasFilteredColimitsOfSize.{w, w} Pointed.{w} where
  HasColimitsOfShape _ _ _ := hasColimitsOfShape_filtered _

/-- The image of `filteredColimitCocone F` under `forget Pointed` is a colimit
cocone in `Type w`. The mapped cocone has tip `(F ⋙ forget Pointed).ColimitType`
and is the canonical Types-cocone obtained from `coconeTypes` via
`coconeTypesEquiv`. -/
noncomputable def filteredColimitMapCoconeIsColimit {J : Type w}
    [SmallCategory J] [IsFiltered J] (F : J ⥤ Pointed.{w}) :
    IsColimit ((forget Pointed.{w}).mapCocone (filteredColimitCocone F)) :=
  ((Limits.Types.isColimit_iff_coconeTypesIsColimit (F := F ⋙ forget Pointed.{w})
    ((forget Pointed.{w}).mapCocone (filteredColimitCocone F))).mpr
    (F ⋙ forget Pointed.{w}).isColimit_coconeTypes).some

/-- The forgetful functor `Pointed ⥤ Type` preserves filtered colimits, since the filtered
colimit of pointed sets is built on the underlying Types-colimit. -/
@[sga "4 I 2.9" "special case"]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget Pointed.{w}) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (filteredColimitCoconeIsColimit F)
        (filteredColimitMapCoconeIsColimit F)⟩

end Pointed_

/-! ## (3) Groups: filling in the missing filtered-colimits instance

Mathlib provides `GrpCat.FilteredColimits.colimitCoconeIsColimit` (an explicit
filtered-colimit witness for a diagram in `GrpCat`) but does not register a
`HasFilteredColimits GrpCat` instance. We do so here. -/

namespace Grp_

/-- `GrpCat` has colimits of every small filtered shape, via Mathlib's explicit
filtered-colimit cocone. -/
instance hasColimitsOfShape_filtered (J : Type w) [SmallCategory J]
    [IsFiltered J] : HasColimitsOfShape J GrpCat.{w} where
  has_colimit F :=
    HasColimit.mk ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit.{w, w} F⟩

/-- `GrpCat` has all small filtered colimits. -/
instance hasFilteredColimits : HasFilteredColimitsOfSize.{w, w} GrpCat.{w} where
  HasColimitsOfShape _ _ _ := hasColimitsOfShape_filtered _

end Grp_

/-! ## (7) Lie algebras over a fixed field

Mathlib does not currently provide a bundled category of Lie algebras over a
field. We introduce `LieAlgCat K` following the standard `Mathlib.Algebra.Category`
pattern, then build its limits and filtered colimits explicitly. -/

/-- The category of Lie algebras over a fixed field `K`: a bundled `K`-Lie
algebra together with `K`-linear Lie algebra homomorphisms. -/
structure LieAlgCat (K : Type w) [Field K] : Type (w+1) where
  /-- The underlying carrier type. -/
  carrier : Type w
  [isLieRing : LieRing carrier]
  [isLieAlgebra : LieAlgebra K carrier]

namespace LieAlgCat

variable {K : Type w} [Field K]

attribute [instance] isLieRing isLieAlgebra

/-- A bundled Lie algebra is coerced to its carrier type. -/
instance : CoeSort (LieAlgCat K) (Type w) := ⟨LieAlgCat.carrier⟩

/-- Construct a bundled `LieAlgCat K` object from the underlying type and
typeclasses. -/
abbrev of (K : Type w) [Field K] (L : Type w) [LieRing L] [LieAlgebra K L] :
    LieAlgCat K := ⟨L⟩

/-- The carrier of `of K L` is `L`. -/
@[simp] lemma coe_of (K : Type w) [Field K] (L : Type w) [LieRing L] [LieAlgebra K L] :
    (of K L : Type w) = L := rfl

/-- Morphisms in `LieAlgCat K` are wrappers around `K`-linear Lie algebra
homomorphisms. -/
@[ext]
structure Hom (L M : LieAlgCat.{w} K) where
  /-- The underlying Lie algebra homomorphism. -/
  hom' : L.carrier →ₗ⁅K⁆ M.carrier

/-- The category structure on `LieAlgCat K`, with composition of the underlying Lie algebra
homomorphisms. -/
instance : Category (LieAlgCat K) where
  Hom L M := Hom L M
  id L := ⟨LieHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/-- `LieAlgCat K` is concrete: its morphisms are Lie algebra homomorphisms of the carriers. -/
instance : ConcreteCategory (LieAlgCat K)
    (fun L M => L.carrier →ₗ⁅K⁆ M.carrier) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying Lie algebra homomorphism of a morphism in `LieAlgCat K`. -/
abbrev Hom.hom {L M : LieAlgCat K} (f : Hom L M) :=
  ConcreteCategory.hom (C := LieAlgCat K) f

/-- The underlying homomorphism of the identity is the identity. -/
@[simp] lemma id_hom (L : LieAlgCat K) :
    (𝟙 L : L ⟶ L).hom = (LieHom.id : L.carrier →ₗ⁅K⁆ L.carrier) := rfl

/-- The underlying homomorphism of a composite is the composite of the underlying ones. -/
@[simp] lemma comp_hom {L M N : LieAlgCat K} (f : L ⟶ M) (g : M ⟶ N) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Two morphisms in `LieAlgCat K` are equal when their underlying homomorphisms are. -/
@[ext] lemma hom_ext {L M : LieAlgCat K} {f g : L ⟶ M}
    (h : f.hom = g.hom) : f = g := by
  obtain ⟨_⟩ := f
  obtain ⟨_⟩ := g
  congr

/-- The forgetful functor `forget (LieAlgCat K)` is faithful. -/
instance forget_faithful : (forget (LieAlgCat K)).Faithful where
  map_injective {_ _} f g h := hom_ext <| LieHom.ext fun x =>
    show (forget (LieAlgCat K)).map f x = (forget (LieAlgCat K)).map g x by rw [h]

/-- The forgetful functor reflects isomorphisms: a Lie algebra homomorphism with
bijective underlying function has a set-theoretic inverse, which inherits
linearity and bracket-preservation by injectivity of the original map. -/
instance forget_reflectsIsomorphisms :
    (forget (LieAlgCat K)).ReflectsIsomorphisms := by
  refine ⟨fun {L M} f hf => ?_⟩
  rw [CategoryTheory.isIso_iff_bijective] at hf
  let fhom : L.carrier →ₗ⁅K⁆ M.carrier := f.hom
  have hbij : Function.Bijective ⇑fhom := hf
  let e : L.carrier ≃ₗ⁅K⁆ M.carrier := LieEquiv.ofBijective fhom hbij
  exact ⟨⟨⟨e.symm.toLieHom⟩, hom_ext (LieHom.ext e.symm_apply_apply),
    hom_ext (LieHom.ext e.apply_symm_apply)⟩⟩

end LieAlgCat

/-! ### Pointwise Lie ring/algebra on a pi-type

A pointwise pi of Lie rings/algebras is again a Lie ring/algebra. Mathlib does
not currently provide these `instance` declarations, so we add them here. -/

section PiLie

variable {I : Type*} (M : I → Type*)

/-- The pointwise bracket on a product of types each carrying a bracket. -/
instance Pi.instBracket [∀ i, Bracket (M i) (M i)] :
    Bracket (∀ i, M i) (∀ i, M i) where
  bracket x y i := ⁅x i, y i⁆

/-- The pointwise bracket is computed componentwise. -/
@[simp] lemma Pi.bracket_apply [∀ i, Bracket (M i) (M i)] (x y : ∀ i, M i) (i : I) :
    (⁅x, y⁆ : ∀ i, M i) i = ⁅x i, y i⁆ := rfl

/-- A product of Lie rings is a Lie ring under the pointwise bracket. -/
@[sga "3 VIIA 5.4" "partial"]
instance Pi.instLieRing [∀ i, LieRing (M i)] : LieRing (∀ i, M i) :=
  { (inferInstance : AddCommGroup (∀ i, M i)) with
    bracket := fun x y i => ⁅x i, y i⁆
    add_lie x y z := funext fun i => add_lie (x i) (y i) (z i)
    lie_add x y z := funext fun i => lie_add (x i) (y i) (z i)
    lie_self x := funext fun i => lie_self (x i)
    leibniz_lie x y z := funext fun i => leibniz_lie (x i) (y i) (z i) }

/-- A product of Lie algebras over `K` is a Lie algebra over `K`. -/
@[sga "3 VIIA 5.4" "partial"]
instance Pi.instLieAlgebra (K : Type*) [CommRing K] [∀ i, LieRing (M i)]
    [∀ i, LieAlgebra K (M i)] : LieAlgebra K (∀ i, M i) :=
  { (inferInstance : Module K (∀ i, M i)) with
    lie_smul t x y := funext fun i => LieAlgebra.lie_smul t (x i) (y i) }

end PiLie

/-! ### Limits in `LieAlgCat K`

The limit of `F : J ⥤ LieAlgCat K` has underlying carrier the Types-limit (a
subset of the product), with pointwise addition, scalar multiplication, and Lie
bracket. -/

namespace LieAlgCat

variable {K : Type w} [Field K]

/-- The proposed limit, realized as a `LieSubalgebra` of the pi-type
`∀ j, (F.obj j).carrier`: tuples compatible with `F.map f` for every `f : j ⟶ j'`. -/
def limitSubalg {J : Type w} [SmallCategory J] (F : J ⥤ LieAlgCat K) :
    LieSubalgebra K (∀ j, (F.obj j).carrier) where
  carrier := { u | ∀ {j j' : J} (f : j ⟶ j'), (F.map f).hom (u j) = u j' }
  add_mem' {a b} ha hb := by
    intro j j' f
    rw [Pi.add_apply, Pi.add_apply, map_add, ha f, hb f]
  zero_mem' := by
    intro j j' f
    exact (F.map f).hom.toLinearMap.map_zero
  smul_mem' c a ha := by
    intro j j' f
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, ha f]
  lie_mem' {a b} ha hb := by
    intro j j' f
    rw [Pi.bracket_apply, Pi.bracket_apply, LieHom.map_lie, ha f, hb f]

/-- The underlying carrier type of the proposed limit. -/
abbrev limitCarrier {J : Type w} [SmallCategory J] (F : J ⥤ LieAlgCat K) : Type w :=
  limitSubalg F

/-- The bundled `LieAlgCat K` object underlying the proposed limit cone. -/
abbrev limitObj {J : Type w} [SmallCategory J] (F : J ⥤ LieAlgCat K) :
    LieAlgCat K := of K (limitCarrier F)

/-- Projection from the proposed limit to `F.obj j`. -/
def limitπ {J : Type w} [SmallCategory J] (F : J ⥤ LieAlgCat K) (j : J) :
    limitObj F ⟶ F.obj j :=
  ⟨{ toFun := fun x => x.val j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     map_lie' := fun {_ _} => rfl }⟩

/-- The proposed limit cone for `F : J ⥤ LieAlgCat K`. -/
def lieAlgLimitCone {J : Type w} [SmallCategory J]
    (F : J ⥤ LieAlgCat K) : Cone F where
  pt := limitObj F
  π :=
    { app := limitπ F
      -- Both sides reduce to `x.val j' = (F.map f).hom (x.val j)`: the constant cone's
      -- naturality against the projection is the compatibility of the tuple `x`.
      naturality _ _ f := hom_ext <| LieHom.ext fun x => (x.property f).symm }

/-- The underlying-set lift of a cone over `F`: send `x : s.pt` to the
compatible tuple `j ↦ (s.π.app j).hom x`. -/
def lieAlgLimitLiftToFun {J : Type w} [SmallCategory J]
    {F : J ⥤ LieAlgCat K} (s : Cone F) (x : s.pt.carrier) : limitCarrier F :=
  ⟨fun j => (s.π.app j).hom x, fun f => ConcreteCategory.congr_hom (s.w f) x⟩

/-- `lieAlgLimitLiftToFun` is additive. -/
lemma lieAlgLimitLiftToFun_add {J : Type w} [SmallCategory J]
    {F : J ⥤ LieAlgCat K} (s : Cone F) (x y : s.pt.carrier) :
    lieAlgLimitLiftToFun s (x + y) =
      lieAlgLimitLiftToFun s x + lieAlgLimitLiftToFun s y :=
  Subtype.ext (funext fun j => map_add (s.π.app j).hom x y)

/-- `lieAlgLimitLiftToFun` commutes with the `K`-action. -/
lemma lieAlgLimitLiftToFun_smul {J : Type w} [SmallCategory J]
    {F : J ⥤ LieAlgCat K} (s : Cone F) (c : K) (x : s.pt.carrier) :
    lieAlgLimitLiftToFun s (c • x) = c • lieAlgLimitLiftToFun s x :=
  Subtype.ext (funext fun j => map_smul (s.π.app j).hom c x)

/-- `lieAlgLimitLiftToFun` preserves the Lie bracket. -/
lemma lieAlgLimitLiftToFun_lie {J : Type w} [SmallCategory J]
    {F : J ⥤ LieAlgCat K} (s : Cone F) (x y : s.pt.carrier) :
    lieAlgLimitLiftToFun s ⁅x, y⁆ = ⁅lieAlgLimitLiftToFun s x, lieAlgLimitLiftToFun s y⁆ :=
  Subtype.ext (funext fun j => (s.π.app j).hom.map_lie x y)

/-- The proposed cone is a limit cone. -/
def lieAlgLimitConeIsLimit {J : Type w} [SmallCategory J]
    (F : J ⥤ LieAlgCat K) : IsLimit (lieAlgLimitCone F) where
  lift s :=
    ⟨{ toFun := lieAlgLimitLiftToFun s
       map_add' := lieAlgLimitLiftToFun_add s
       map_smul' := lieAlgLimitLiftToFun_smul s
       map_lie' := fun {x y} => lieAlgLimitLiftToFun_lie s x y }⟩
  fac _ _ := hom_ext (LieHom.ext fun _ => rfl)
  uniq _ _ h := hom_ext <| LieHom.ext fun x => Subtype.ext <| funext fun j =>
    ConcreteCategory.congr_hom (h j) x

/-- `LieAlgCat K` has limits of every small shape, given by `lieAlgLimitCone`. -/
instance hasLimitsOfShape (J : Type w) [SmallCategory J] :
    HasLimitsOfShape J (LieAlgCat K) where
  has_limit F := ⟨_, lieAlgLimitConeIsLimit F⟩

/-- `LieAlgCat K` has all small limits. -/
instance hasLimits : HasLimitsOfSize.{w, w} (LieAlgCat K) where
  has_limits_of_shape _ _ := hasLimitsOfShape _

/-- The image of `lieAlgLimitCone F` under `forget (LieAlgCat K)` is a limit cone
in `Type w`: it is literally the standard `Types.limitCone`. -/
noncomputable def lieAlgLimitMapConeIsLimit {J : Type w} [SmallCategory J]
    (F : J ⥤ LieAlgCat K) :
    IsLimit ((forget (LieAlgCat K)).mapCone (lieAlgLimitCone F)) :=
  Types.limitConeIsLimit (F ⋙ forget (LieAlgCat K))

/-- The forgetful functor `forget (LieAlgCat K)` preserves limits. -/
instance forget_preservesLimitsOfShape (J : Type w) [SmallCategory J] :
    PreservesLimitsOfShape J (forget (LieAlgCat K)) where
  preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (lieAlgLimitConeIsLimit F)
      (lieAlgLimitMapConeIsLimit F)

/-- The forgetful functor `LieAlgCat K ⥤ Type` preserves all small limits. -/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, w} (forget (LieAlgCat K)) where
  preservesLimitsOfShape := forget_preservesLimitsOfShape _

end LieAlgCat

/-! ### Filtered colimits in `LieAlgCat K`

A filtered colimit `M` of `F : J ⥤ LieAlgCat K` is realized via the Types-colimit
with addition, scalar multiplication and the Lie bracket defined on
representatives at a common upper bound, well-defined by filteredness of `J` and
the fact that the structure maps preserve them. We follow the pattern of
`Mathlib.Algebra.Category.MonCat.FilteredColimits` etc.

We forget through the underlying `ModuleCat K`: the filtered colimit `M` in
`ModuleCat K` carries a Lie bracket via representatives. -/

namespace LieAlgCat

variable {K : Type w} [Field K]

/-- The forgetful functor from `LieAlgCat K` to `ModuleCat K`. -/
@[implicit_reducible]
def toModuleCat : LieAlgCat.{w} K ⥤ ModuleCat.{w} K where
  obj L := ModuleCat.of K L.carrier
  map {L M} f := ModuleCat.ofHom f.hom.toLinearMap

/-- The linear map underlying `toModuleCat.map f` is the underlying map of `f`. -/
lemma toModuleCat_map_hom_apply {L M : LieAlgCat.{w} K} (f : L ⟶ M) (x : L.carrier) :
    (toModuleCat.map f).hom x = f.hom x :=
  rfl

/-- The forgetful functor `toModuleCat` composed with `forget (ModuleCat K)` is
the forgetful functor `forget (LieAlgCat K)` as a functor. -/
lemma toModuleCat_forget_eq (L : LieAlgCat K) :
    (toModuleCat ⋙ forget (ModuleCat.{w} K)).obj L =
      (forget (LieAlgCat K)).obj L := rfl

/-- The carrier map of a composite in the index category is the composite of the carrier
maps. -/
lemma map_hom_comp_apply {J : Type*} [Category J] (F : J ⥤ LieAlgCat.{w} K)
    {i k s : J} (p : i ⟶ k) (α : k ⟶ s) (a : (F.obj i).carrier) :
    (F.map (p ≫ α)).hom a = (F.map α).hom ((F.map p).hom a) := by
  rw [F.map_comp]
  rfl

/-- Two paths out of `i` with equal composites induce the same map on carriers. -/
lemma map_hom_apply_eq_of_comp_eq {J : Type*} [Category J] (F : J ⥤ LieAlgCat.{w} K)
    {i k k' s : J} {p : i ⟶ k} {α : k ⟶ s} {q : i ⟶ k'} {β : k' ⟶ s}
    (h : p ≫ α = q ≫ β) (a : (F.obj i).carrier) :
    (F.map α).hom ((F.map p).hom a) = (F.map β).hom ((F.map q).hom a) := by
  rw [← map_hom_comp_apply, ← map_hom_comp_apply, h]

variable {J : Type w} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ LieAlgCat K)

/-- The bundled module underlying the proposed filtered colimit: the
filtered colimit of `F ⋙ toModuleCat` in `ModuleCat K`. -/
noncomputable abbrev fcolimitModule : ModuleCat.{w} K :=
  ModuleCat.FilteredColimits.colimit.{w, w} (F ⋙ toModuleCat)

/-- The underlying type of the proposed filtered colimit. -/
noncomputable abbrev fcolimitCarrier : Type w := fcolimitModule F

/-- Canonical map from `(F.obj j).carrier` to the colimit, via
`ModuleCat.FilteredColimits.M.mk`. -/
noncomputable def fcolimitMk (j : J) (x : (F.obj j).carrier) : fcolimitCarrier F :=
  ModuleCat.FilteredColimits.M.mk (F ⋙ toModuleCat) ⟨j, x⟩

/-- Every element of the filtered colimit is `fcolimitMk F j x` for some index `j`. -/
lemma fcolimitMk_surjective (m : fcolimitCarrier F) :
    ∃ (j : J) (x : (F.obj j).carrier), fcolimitMk F j x = m :=
  ModuleCat.FilteredColimits.M.mk_surjective _ m

/-- Two representatives define the same element of the colimit as soon as they agree after
being pushed to a common upper bound. -/
lemma fcolimitMk_eq {j j' : J} (x : (F.obj j).carrier) (y : (F.obj j').carrier)
    {k : J} (f : j ⟶ k) (g : j' ⟶ k)
    (h : (F.map f).hom x = (F.map g).hom y) :
    fcolimitMk F j x = fcolimitMk F j' y :=
  ModuleCat.FilteredColimits.M.mk_eq _ _ _ ⟨k, f, g, by
    rwa [Functor.comp_map, Functor.comp_map, toModuleCat_map_hom_apply,
      toModuleCat_map_hom_apply]⟩

/-- `fcolimitMk` is compatible with the structure maps of the diagram. -/
@[simp] lemma fcolimitMk_map {j k : J} (f : j ⟶ k) (x : (F.obj j).carrier) :
    fcolimitMk F k ((F.map f).hom x) = fcolimitMk F j x :=
  ModuleCat.FilteredColimits.M.mk_map (F ⋙ toModuleCat) f x

/-- Any two elements of the filtered colimit are represented at a common index. -/
lemma fcolimitMk_surjective₂ (m n : fcolimitCarrier F) :
    ∃ (j : J) (x y : (F.obj j).carrier),
      fcolimitMk F j x = m ∧ fcolimitMk F j y = n := by
  obtain ⟨i, x, rfl⟩ := fcolimitMk_surjective F m
  obtain ⟨j, y, rfl⟩ := fcolimitMk_surjective F n
  exact ⟨IsFiltered.max i j, (F.map (IsFiltered.leftToMax i j)).hom x,
    (F.map (IsFiltered.rightToMax i j)).hom y, fcolimitMk_map .., fcolimitMk_map ..⟩

/-- Any three elements of the filtered colimit are represented at a common index. -/
lemma fcolimitMk_surjective₃ (m n p : fcolimitCarrier F) :
    ∃ (j : J) (x y z : (F.obj j).carrier),
      fcolimitMk F j x = m ∧ fcolimitMk F j y = n ∧ fcolimitMk F j z = p := by
  obtain ⟨i, x, rfl⟩ := fcolimitMk_surjective F m
  obtain ⟨j, y, rfl⟩ := fcolimitMk_surjective F n
  obtain ⟨k, z, rfl⟩ := fcolimitMk_surjective F p
  exact ⟨IsFiltered.max₃ i j k, (F.map (IsFiltered.firstToMax₃ i j k)).hom x,
    (F.map (IsFiltered.secondToMax₃ i j k)).hom y,
    (F.map (IsFiltered.thirdToMax₃ i j k)).hom z,
    fcolimitMk_map .., fcolimitMk_map .., fcolimitMk_map ..⟩

/-- Addition in the filtered colimit is computed on representatives at a common upper bound. -/
lemma fcolimit_add_mk_eq (x : Σ j, (F.obj j).carrier)
    (y : Σ j, (F.obj j).carrier) (k : J)
    (f : x.fst ⟶ k) (g : y.fst ⟶ k) :
    fcolimitMk F x.fst x.snd + fcolimitMk F y.fst y.snd =
      fcolimitMk F k ((F.map f).hom x.snd + (F.map g).hom y.snd) := by
  refine (ModuleCat.FilteredColimits.colimit_add_mk_eq (F ⋙ toModuleCat) x y k f g).trans ?_
  rfl

/-- Addition of two representatives at the *same* index is computed at that index. -/
lemma fcolimit_add_mk_eq' {j : J} (x y : (F.obj j).carrier) :
    fcolimitMk F j x + fcolimitMk F j y = fcolimitMk F j (x + y) :=
  ModuleCat.FilteredColimits.colimit_add_mk_eq' (F ⋙ toModuleCat) x y

/-- The `K`-action on the filtered colimit is computed on representatives. -/
@[simp] lemma fcolimit_smul_mk_eq (c : K) (j : J) (x : (F.obj j).carrier) :
    c • fcolimitMk F j x = fcolimitMk F j (c • x) :=
  ModuleCat.FilteredColimits.colimit_smul_mk_eq (F ⋙ toModuleCat) c ⟨j, x⟩

/-- Zero in the filtered colimit is the class of zero at any index. -/
lemma fcolimit_zero_eq (j : J) :
    (0 : fcolimitCarrier F) = fcolimitMk F j 0 :=
  ModuleCat.FilteredColimits.colimit_zero_eq (F ⋙ toModuleCat) j

/-! ### The Lie bracket on the filtered colimit

The bracket on the filtered colimit is the unique `K`-bilinear map `b : M × M → M`
such that the `j`-th component restricts to the Lie bracket of `F.obj j`. We
realize this directly using `Quot.lift` and the bracket on representatives at a
common upper bound. Well-definedness is forced by filteredness and the fact
that the structure maps `F.map f` preserve the bracket. -/

/-- Auxiliary bracket on representatives at a common upper bound `k`. -/
noncomputable def fcolimitBracketAtUB
    {i j k : J} (α : i ⟶ k) (β : j ⟶ k)
    (x : (F.obj i).carrier) (y : (F.obj j).carrier) : fcolimitCarrier F :=
  fcolimitMk F k ⁅(F.map α).hom x, (F.map β).hom y⁆

/-- Independence of `fcolimitBracketAtUB` on the choice of upper bound. -/
lemma fcolimitBracketAtUB_indep {i j : J} (x : (F.obj i).carrier) (y : (F.obj j).carrier)
    {k : J} (α : i ⟶ k) (β : j ⟶ k)
    {k' : J} (α' : i ⟶ k') (β' : j ⟶ k') :
    fcolimitBracketAtUB F α β x y = fcolimitBracketAtUB F α' β' x y := by
  obtain ⟨ℓ, γ, γ', hα, hβ⟩ :=
    IsFiltered.bowtie (j₁ := i) (j₂ := j) (k₁ := k) (k₂ := k') α α' β β'
  refine fcolimitMk_eq F _ _ γ γ' ?_
  rw [(F.map γ).hom.map_lie, (F.map γ').hom.map_lie,
    map_hom_apply_eq_of_comp_eq F hα x, map_hom_apply_eq_of_comp_eq F hβ y]

/-- The bracket on representatives `(j₁, x)` and `(j₂, y)`, using the canonical
`leftToMax`/`rightToMax` morphisms to a common upper bound. -/
noncomputable def fcolimitBracketRepr (x : Σ j, (F.obj j).carrier)
    (y : Σ j, (F.obj j).carrier) : fcolimitCarrier F :=
  fcolimitBracketAtUB F (IsFiltered.leftToMax x.fst y.fst)
    (IsFiltered.rightToMax x.fst y.fst) x.snd y.snd

/-- `fcolimitBracketRepr` may be computed at any common upper bound of the two indices. -/
lemma fcolimitBracketRepr_eq_atUB (x y : Σ j, (F.obj j).carrier) {k : J}
    (α : x.fst ⟶ k) (β : y.fst ⟶ k) :
    fcolimitBracketRepr F x y =
      fcolimitMk F k ⁅(F.map α).hom x.snd, (F.map β).hom y.snd⁆ :=
  fcolimitBracketAtUB_indep F x.snd y.snd _ _ α β

/-- Brackets of representatives agree once both are pushed to a common upper bound with equal
images. -/
private lemma fcolimitBracketRepr_eq_of_map_eq (x x' y y' : Σ j, (F.obj j).carrier) {k : J}
    (α : x.fst ⟶ k) (α' : x'.fst ⟶ k) (β : y.fst ⟶ k) (β' : y'.fst ⟶ k)
    (hx : (F.map α).hom x.snd = (F.map α').hom x'.snd)
    (hy : (F.map β).hom y.snd = (F.map β').hom y'.snd) :
    fcolimitBracketRepr F x y = fcolimitBracketRepr F x' y' := by
  rw [fcolimitBracketRepr_eq_atUB F x y α β, fcolimitBracketRepr_eq_atUB F x' y' α' β', hx, hy]

/-- The right-side rel form of independence: if `y, y'` are related by the
filtered-colimit relation, then `fcolimitBracketRepr F x y = fcolimitBracketRepr F x y'`. -/
lemma fcolimitBracketRepr_eq_of_rel_right (x : Σ j, (F.obj j).carrier)
    {y y' : Σ j, (F.obj j).carrier}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget (LieAlgCat K)) y y') :
    fcolimitBracketRepr F x y = fcolimitBracketRepr F x y' := by
  obtain ⟨l, f, g, hfg⟩ := hyy'
  exact fcolimitBracketRepr_eq_of_map_eq F x x y y' (IsFiltered.leftToMax x.fst l)
    (IsFiltered.leftToMax x.fst l) (f ≫ IsFiltered.rightToMax x.fst l)
    (g ≫ IsFiltered.rightToMax x.fst l) rfl
    (by rw [map_hom_comp_apply, map_hom_comp_apply]; exact congrArg _ hfg)

/-- The left-side rel form of independence. -/
lemma fcolimitBracketRepr_eq_of_rel_left {x x' : Σ j, (F.obj j).carrier}
    (y : Σ j, (F.obj j).carrier)
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget (LieAlgCat K)) x x') :
    fcolimitBracketRepr F x y = fcolimitBracketRepr F x' y := by
  obtain ⟨l, f, g, hfg⟩ := hxx'
  exact fcolimitBracketRepr_eq_of_map_eq F x x' y y (f ≫ IsFiltered.leftToMax l y.fst)
    (g ≫ IsFiltered.leftToMax l y.fst) (IsFiltered.rightToMax l y.fst)
    (IsFiltered.rightToMax l y.fst)
    (by rw [map_hom_comp_apply, map_hom_comp_apply]; exact congrArg _ hfg) rfl

/-- The Lie bracket on the filtered colimit, via `Quot.lift₂`. -/
noncomputable instance fcolimitBracket : Bracket (fcolimitCarrier F) (fcolimitCarrier F) where
  bracket x y := Quot.lift₂ (fcolimitBracketRepr F)
    (fun _ _ _ h => fcolimitBracketRepr_eq_of_rel_right _ _
      (Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h))
    (fun _ _ _ h => fcolimitBracketRepr_eq_of_rel_left _ _
      (Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h)) x y

/-- Bracket of `mk i x, mk j y` equals `mk k ⁅F.map f x, F.map g y⁆` for any common upper
bound `k` with morphisms `f : i ⟶ k`, `g : j ⟶ k`. -/
lemma fcolimit_lie_mk_eq (x y : Σ j, (F.obj j).carrier) (k : J)
    (f : x.fst ⟶ k) (g : y.fst ⟶ k) :
    ⁅fcolimitMk F x.fst x.snd, fcolimitMk F y.fst y.snd⁆ =
      fcolimitMk F k ⁅(F.map f).hom x.snd, (F.map g).hom y.snd⁆ := by
  obtain ⟨j₁, x⟩ := x
  obtain ⟨j₂, y⟩ := y
  show fcolimitBracketRepr F ⟨j₁, x⟩ ⟨j₂, y⟩ = _
  exact fcolimitBracketRepr_eq_atUB F ⟨j₁, x⟩ ⟨j₂, y⟩ f g

/-- Convenience: bracket of two mk's at the same index. -/
lemma fcolimit_lie_mk_eq' {j : J} (x y : (F.obj j).carrier) :
    ⁅fcolimitMk F j x, fcolimitMk F j y⁆ = fcolimitMk F j ⁅x, y⁆ := by
  simpa using fcolimit_lie_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

/-- The filtered colimit carries a `LieRing` structure. -/
noncomputable instance fcolimitLieRing : LieRing (fcolimitCarrier F) :=
  { (inferInstance : AddCommGroup (fcolimitCarrier F)) with
    bracket := fun x y => ⁅x, y⁆
    add_lie := fun x y z => by
      obtain ⟨j, x, y, z, rfl, rfl, rfl⟩ := fcolimitMk_surjective₃ F x y z
      rw [fcolimit_add_mk_eq' F x y, fcolimit_lie_mk_eq' F (x + y) z,
        fcolimit_lie_mk_eq' F x z, fcolimit_lie_mk_eq' F y z,
        fcolimit_add_mk_eq' F ⁅x, z⁆ ⁅y, z⁆, add_lie]
    lie_add := fun x y z => by
      obtain ⟨j, x, y, z, rfl, rfl, rfl⟩ := fcolimitMk_surjective₃ F x y z
      rw [fcolimit_add_mk_eq' F y z, fcolimit_lie_mk_eq' F x (y + z),
        fcolimit_lie_mk_eq' F x y, fcolimit_lie_mk_eq' F x z,
        fcolimit_add_mk_eq' F ⁅x, y⁆ ⁅x, z⁆, lie_add]
    lie_self := fun x => by
      obtain ⟨i, x, rfl⟩ := fcolimitMk_surjective F x
      rw [fcolimit_lie_mk_eq' F x x, lie_self, ← fcolimit_zero_eq F i]
    leibniz_lie := fun x y z => by
      obtain ⟨j, x, y, z, rfl, rfl, rfl⟩ := fcolimitMk_surjective₃ F x y z
      rw [fcolimit_lie_mk_eq' F y z, fcolimit_lie_mk_eq' F x ⁅y, z⁆,
        fcolimit_lie_mk_eq' F x y, fcolimit_lie_mk_eq' F ⁅x, y⁆ z,
        fcolimit_lie_mk_eq' F x z, fcolimit_lie_mk_eq' F y ⁅x, z⁆,
        fcolimit_add_mk_eq' F ⁅⁅x, y⁆, z⁆ ⁅y, ⁅x, z⁆⁆, leibniz_lie] }

/-- The filtered colimit carries a `LieAlgebra K` structure. -/
noncomputable instance fcolimitLieAlgebra : LieAlgebra K (fcolimitCarrier F) :=
  { (inferInstance : Module K (fcolimitCarrier F)) with
    lie_smul := fun t x y => by
      obtain ⟨j, x, y, rfl, rfl⟩ := fcolimitMk_surjective₂ F x y
      rw [fcolimit_smul_mk_eq F t j y, fcolimit_lie_mk_eq' F x (t • y),
        fcolimit_lie_mk_eq' F x y, fcolimit_smul_mk_eq F t j ⁅x, y⁆, lie_smul] }

/-- The bundled `LieAlgCat K` object underlying the proposed filtered colimit cocone. -/
noncomputable abbrev fcolimitObj : LieAlgCat K := of K (fcolimitCarrier F)

/-- The cocone-inclusion map from `F.obj j` to the filtered colimit, as a Lie hom. -/
noncomputable def fcolimitιLieHom (j : J) :
    (F.obj j).carrier →ₗ⁅K⁆ fcolimitCarrier F where
  toFun x := fcolimitMk F j x
  map_add' x y := (fcolimit_add_mk_eq' F x y).symm
  map_smul' c x := (fcolimit_smul_mk_eq F c j x).symm
  map_lie' {x y} := (fcolimit_lie_mk_eq' F x y).symm

/-- The cocone-inclusion map from `F.obj j` to the filtered colimit. -/
noncomputable def fcolimitι (j : J) : F.obj j ⟶ fcolimitObj F :=
  ⟨fcolimitιLieHom F j⟩

/-- The proposed filtered colimit cocone. -/
noncomputable def fcolimitCocone : Cocone F where
  pt := fcolimitObj F
  ι :=
    { app := fcolimitι F
      naturality _ _ f := hom_ext (LieHom.ext fun x => fcolimitMk_map F f x) }

/-- The descent of a cocone `s` from the filtered colimit, as a Lie hom. The
underlying function is `descColimitType` applied to the cocone whose `ι.app j`
sends `x` to `(s.ι.app j).hom x`. -/
noncomputable def fcolimitDescLieHom (s : Cocone F) :
    fcolimitCarrier F →ₗ⁅K⁆ s.pt.carrier where
  toFun :=
    (F ⋙ forget (LieAlgCat K)).descColimitType
      { pt := s.pt.carrier
        ι := fun j x => (s.ι.app j).hom x
        ι_naturality f := funext (ConcreteCategory.congr_hom (s.w f)) }
  map_add' x y := by
    obtain ⟨m, x, y, rfl, rfl⟩ := fcolimitMk_surjective₂ F x y
    rw [fcolimit_add_mk_eq' F x y]
    change (s.ι.app m).hom (x + y) = (s.ι.app m).hom x + (s.ι.app m).hom y
    exact (s.ι.app m).hom.toLinearMap.map_add _ _
  map_smul' c x := by
    obtain ⟨i, x, rfl⟩ := fcolimitMk_surjective F x
    rw [fcolimit_smul_mk_eq F c i x]
    change (s.ι.app i).hom (c • x) = c • (s.ι.app i).hom x
    exact (s.ι.app i).hom.toLinearMap.map_smul c x
  map_lie' {x y} := by
    obtain ⟨m, x, y, rfl, rfl⟩ := fcolimitMk_surjective₂ F x y
    rw [fcolimit_lie_mk_eq' F x y]
    change (s.ι.app m).hom ⁅x, y⁆ = ⁅(s.ι.app m).hom x, (s.ι.app m).hom y⁆
    exact (s.ι.app m).hom.map_lie _ _

/-- The descent of a cocone `s` from the filtered colimit. -/
noncomputable def fcolimitDesc (s : Cocone F) : fcolimitObj F ⟶ s.pt :=
  ⟨fcolimitDescLieHom F s⟩

/-- The proposed filtered colimit cocone is a colimit cocone. -/
noncomputable def fcolimitCoconeIsColimit : IsColimit (fcolimitCocone F) where
  desc := fcolimitDesc F
  fac _ _ := hom_ext (LieHom.ext fun _ => rfl)
  uniq s m h := hom_ext <| LieHom.ext fun x => by
    obtain ⟨j, y, rfl⟩ :=
      (F ⋙ forget (LieAlgCat K)).ιColimitType_jointly_surjective x
    exact ConcreteCategory.congr_hom (h j) y

/-- `LieAlgCat K` has colimits of every small filtered shape, given by `fcolimitCocone`. -/
instance hasColimitsOfShape_filtered (J : Type w) [SmallCategory J] [IsFiltered J] :
    HasColimitsOfShape J (LieAlgCat K) where
  has_colimit F := ⟨_, fcolimitCoconeIsColimit F⟩

/-- `LieAlgCat K` has all small filtered colimits. -/
instance hasFilteredColimits : HasFilteredColimitsOfSize.{w, w} (LieAlgCat K) where
  HasColimitsOfShape _ _ _ := hasColimitsOfShape_filtered _

/-- The image of `fcolimitCocone F` under `forget (LieAlgCat K)` is a colimit
cocone in `Type w`. -/
noncomputable def fcolimitMapCoconeIsColimit (F : J ⥤ LieAlgCat K) :
    IsColimit ((forget (LieAlgCat K)).mapCocone (fcolimitCocone F)) :=
  ((Limits.Types.isColimit_iff_coconeTypesIsColimit (F := F ⋙ forget (LieAlgCat K))
    ((forget (LieAlgCat K)).mapCocone (fcolimitCocone F))).mpr
    (F ⋙ forget (LieAlgCat K)).isColimit_coconeTypes).some

/-- The forgetful functor `LieAlgCat K ⥤ Type` preserves filtered colimits, since the filtered
colimit of Lie algebras is built on the underlying Types-colimit. -/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (LieAlgCat K)) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (fcolimitCoconeIsColimit F)
        (fcolimitMapCoconeIsColimit F)⟩

end LieAlgCat

/-! ## The 7 theorems of Stacks 007N

Each item states that the named category, together with its forgetful functor to
`Type`, satisfies `IsTypeOfAlgebraicStructure`. -/

/-- **Item (1).** The category of pointed sets is a type of
algebraic structures (with the forgetful functor to `Type`). -/
@[stacks 007N "(1)"]
theorem isTypeOfAlgebraicStructure_pointed :
    IsTypeOfAlgebraicStructure Pointed.{w} (forget Pointed.{w}) where
  faithful := inferInstance
  hasLimits := Pointed_.hasLimits
  preservesLimits := inferInstance
  hasFilteredColimits := Pointed_.hasFilteredColimits
  preservesFilteredColimits := Pointed_.forget_preservesFilteredColimits
  reflectsIsomorphisms := Pointed_.forget_reflectsIsomorphisms

/-- **Item (2).** The category of abelian groups is a type of
algebraic structures. -/
@[stacks 007N "(2)"]
theorem isTypeOfAlgebraicStructure_addCommGrpCat :
    IsTypeOfAlgebraicStructure AddCommGrpCat.{w} (forget AddCommGrpCat.{w}) where
  faithful := inferInstance
  hasLimits := inferInstance
  preservesLimits := inferInstance
  hasFilteredColimits := inferInstance
  preservesFilteredColimits := inferInstance
  reflectsIsomorphisms := inferInstance

/-- **Item (3).** The category of groups is a type of algebraic
structures. -/
@[stacks 007N "(3)"]
theorem isTypeOfAlgebraicStructure_grpCat :
    IsTypeOfAlgebraicStructure GrpCat.{w} (forget GrpCat.{w}) where
  faithful := inferInstance
  hasLimits := inferInstance
  preservesLimits := inferInstance
  hasFilteredColimits := Grp_.hasFilteredColimits
  preservesFilteredColimits := inferInstance
  reflectsIsomorphisms := inferInstance

/-- **Item (4).** The category of monoids is a type of algebraic
structures. -/
@[stacks 007N "(4)"]
theorem isTypeOfAlgebraicStructure_monCat :
    IsTypeOfAlgebraicStructure MonCat.{w} (forget MonCat.{w}) where
  faithful := inferInstance
  hasLimits := inferInstance
  preservesLimits := inferInstance
  hasFilteredColimits := inferInstance
  preservesFilteredColimits := inferInstance
  reflectsIsomorphisms := inferInstance

/-- **Item (5).** The category of commutative rings is a type of
algebraic structures. (In the Stacks Project, a ring is a commutative ring with
unit, so the appropriate Mathlib category is `CommRingCat`.) -/
@[stacks 007N "(5)"]
theorem isTypeOfAlgebraicStructure_commRingCat :
    IsTypeOfAlgebraicStructure CommRingCat.{w} (forget CommRingCat.{w}) where
  faithful := inferInstance
  hasLimits := inferInstance
  preservesLimits := inferInstance
  hasFilteredColimits := inferInstance
  preservesFilteredColimits := inferInstance
  reflectsIsomorphisms := inferInstance

/-- **Item (6).** For any fixed commutative ring `R`, the category
of `R`-modules is a type of algebraic structures. -/
@[stacks 007N "(6)"]
theorem isTypeOfAlgebraicStructure_moduleCat (R : Type w) [CommRing R] :
    IsTypeOfAlgebraicStructure (ModuleCat.{w} R) (forget (ModuleCat.{w} R)) where
  faithful := inferInstance
  hasLimits := inferInstance
  preservesLimits := inferInstance
  hasFilteredColimits := inferInstance
  preservesFilteredColimits := inferInstance
  reflectsIsomorphisms := inferInstance

/-- **Item (7).** For any fixed field `K`, the category of `K`-Lie
algebras is a type of algebraic structures. -/
@[stacks 007N "(7)"]
theorem isTypeOfAlgebraicStructure_lieAlgCat (K : Type w) [Field K] :
    IsTypeOfAlgebraicStructure (LieAlgCat K) (forget (LieAlgCat K)) where
  faithful := inferInstance
  hasLimits := LieAlgCat.hasLimits
  preservesLimits := LieAlgCat.forget_preservesLimitsOfSize
  hasFilteredColimits := LieAlgCat.hasFilteredColimits
  preservesFilteredColimits := LieAlgCat.forget_preservesFilteredColimits
  reflectsIsomorphisms := LieAlgCat.forget_reflectsIsomorphisms

/-! ## Bridging the predicate and the bundle

Without these two, the seven facts above are unusable: every theorem about a type of algebraic
structure takes the bundle `AlgebraicStructureType`, so a proof that `GrpCat` satisfies the
predicate could not be handed to any of them. -/

/-- Package a `(C, F)` satisfying the predicate as the bundled `AlgebraicStructureType` that
carries the 007M tag. -/
noncomputable def IsTypeOfAlgebraicStructure.toAlgebraicStructureType
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    (h : IsTypeOfAlgebraicStructure C F) : AlgebraicStructureType.{v, u} :=
  haveI := h.faithful
  haveI := h.hasLimits
  haveI := h.preservesLimits
  haveI := h.hasFilteredColimits
  haveI := h.preservesFilteredColimits
  haveI := h.reflectsIsomorphisms
  { C := C, F := F }

/-- Conversely, the underlying `(C, F)` of a bundled type of algebraic structure satisfies the
predicate. -/
theorem AlgebraicStructureType.isTypeOfAlgebraicStructure (A : AlgebraicStructureType.{v, u}) :
    IsTypeOfAlgebraicStructure A.C A.F :=
  { faithful := inferInstance
    hasLimits := inferInstance
    preservesLimits := inferInstance
    hasFilteredColimits := inferInstance
    preservesFilteredColimits := inferInstance
    reflectsIsomorphisms := inferInstance }
