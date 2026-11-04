module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The derived tensor product of a ringed site is right t-exact

Let `(C, O)` be a ringed site and let `K`, `L` be objects of `D(Mod(O))` with `H^i(K) = 0` for
`i > a` and `H^j(L) = 0` for `j > b`. Then `H^i(K ⊗_O^{L} L) = 0` for `i > a + b`; that is,
the derived tensor product is right t-exact in both variables for the canonical t-structure,
with the two bounds added.

The proof is the usual one. A bounded above object of the derived category is represented by a
complex which is bounded above *strictly*, in the sense that its terms vanish above the bound,
and whose terms are moreover flat: Stacks 05T7 resolves a representative by such a complex,
and Stacks 06YQ makes it K-flat. On two K-flat representatives the derived tensor product is
the ordinary total tensor complex, by the two-sided comparison of Stacks 06YU; and every
summand `F^p ⊗_O G^q` of the term of that complex in a degree `i > a + b` has `p > a` or
`q > b`, so one factor vanishes and the summand with it.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.flatModules`: flatness of a sheaf of `O`-modules, read as a
  property of the objects of `Mod(O)`.
* `Stacks.DerivedTensor.RingedSite.derivedTensorProductIso`: the derived tensor product of two
  objects of `D(Mod(O))` represented by K-flat complexes is the total tensor complex of those
  complexes.

## Main results

* `Stacks.DerivedTensor.RingedSite.isStrictlyLE_mapBifunctor`: the total tensor complex of two
  complexes vanishing above `a` and above `b` vanishes above `a + b`.
* `Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative`: an object of
  `D^{≤ a}(Mod(O))` is represented by a K-flat complex whose terms vanish above `a`.
* `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`: **right t-exactness**, for an
  arbitrary derived tensor product of Stacks 06YU.
* `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`: the same for the
  canonical one.

## Implementation notes

The hypotheses and universes are those of
`Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct`, which is where the narrowing of
the site to a small one with all four universes equal comes from; nothing is narrowed here.

Flatness is carried as the object property `flatModules` rather than inline because Stacks
05T7 asks for `CategoryTheory.ObjectProperty.ContainsZero`, which is an instance on a named
property. The flat cover it also asks for is
`Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat`, used inline.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u d

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Flatness of a sheaf of `O`-modules, read as a property of the objects of `Mod(O)`. -/
abbrev flatModules : ObjectProperty (Modules R) :=
  fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M

/-- **The zero sheaf of modules is flat**, so the flat sheaves of modules are a class of
objects of the kind Stacks 05T7 resolves by. -/
instance containsZero_flatModules : (flatModules R).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero R (isZero_zero _)⟩

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The total tensor complex of two bounded above complexes is bounded above**, with the two
bounds added. Every summand `P^p ⊗_O Q^q` of the term in a degree `i > a + b` has `p > a` or
`q > b`, so one factor vanishes and the summand vanishes with it. -/
theorem isStrictlyLE_mapBifunctor (P Q : CochainComplex (Modules R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (HomologicalComplex.mapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X p)).obj (Q.X q)) := by
    by_cases hp : a < p
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).map_isZero
        (P.isZero_of_isStrictlyLE a p hp)).obj _
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyLE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

variable [HasDerivedCategory.{d} (Modules R)]

/-- **A bounded above object of `D(Mod(O))` has a K-flat representative with the same bound.**
Stacks 05T7 resolves a representative by a complex with zero terms above `a` and flat terms —
flatness being an object property which contains a zero object and with every sheaf of modules
a quotient of a flat one — and Stacks 06YQ makes that complex K-flat. -/
theorem exists_kFlat_isStrictlyLE_representative (K : DerivedModules R) (a : ℤ) [K.IsLE a] :
    ∃ F : CochainComplex (Modules R) ℤ,
      Stacks.SheafOfModules.KFlat.KFlat R F ∧ F.IsStrictlyLE a ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have hPLE : P.IsLE a :=
    (DerivedCategory.isLE_Q_obj_iff P a).1
      (DerivedCategory.TStructure.t.isLE_of_iso eP.symm a)
  obtain ⟨F, f, hf, hFflat, hFLE⟩ :=
    (CochainComplex.exists_quasiIso_prop (flatModules R)
      (fun M => by
        obtain ⟨N, π, hflat, hepi⟩ :=
          Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat R M
        exact ⟨N, hflat, π, hepi⟩) a).2 P
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨F, Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat R F ⟨a, hFLE⟩ hFflat, hFLE,
    ⟨asIso (DerivedCategory.Q.map f) ≪≫ eP⟩⟩

/-- **The derived tensor product of two objects represented by K-flat complexes is the total
tensor complex of those complexes.** This is the two-sided comparison of Stacks 06YU,
transported along the two chosen representatives. -/
def derivedTensorProductIso (T : DerivedTensorProduct R) {K L : DerivedModules R}
    {F G : CochainComplex (Modules R) ℤ}
    (hF : Stacks.SheafOfModules.KFlat.KFlat R F) (hG : Stacks.SheafOfModules.KFlat.KFlat R G)
    (eF : DerivedCategory.Q.obj F ≅ K) (eG : DerivedCategory.Q.obj G ≅ L) :
    (T.tensor.obj K).obj L ≅ DerivedCategory.Q.obj
      (HomologicalComplex.mapBifunctor F G (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)) :=
  (T.tensor.mapIso eF.symm).app L ≪≫ (T.tensor.obj _).mapIso eG.symm ≪≫ T.comparison F G hF hG

/-- **The derived tensor product is right t-exact in both variables**: the derived tensor
product of an object of `D^{≤ a}(Mod(O))` with an object of `D^{≤ b}(Mod(O))` lies in
`D^{≤ a + b}(Mod(O))`. Both factors are represented by K-flat complexes with zero terms above
their own bounds, on which the derived tensor product is the total tensor complex, and that
complex has zero terms above the sum. -/
theorem isLE_derivedTensorProduct (T : DerivedTensorProduct R) (K L : DerivedModules R) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] : ((T.tensor.obj K).obj L).IsLE (a + b) := by
  obtain ⟨F, hF, hFLE, ⟨eF⟩⟩ := exists_kFlat_isStrictlyLE_representative R K a
  obtain ⟨G, hG, hGLE, ⟨eG⟩⟩ := exists_kFlat_isStrictlyLE_representative R L b
  have := hFLE
  have := hGLE
  have hTot : (DerivedCategory.Q.obj
      (HomologicalComplex.mapBifunctor F G (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ))).IsLE (a + b) := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    have := isStrictlyLE_mapBifunctor R F G a b
    infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (derivedTensorProductIso R T hF hG eF eG).symm (a + b)

/-- **Right t-exactness of the canonical derived tensor product of a ringed site.** -/
theorem isLE_derivedTensorProductFunctor (K L : DerivedModules R) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] :
    (((derivedTensorProductFunctor R).obj K).obj L).IsLE (a + b) :=
  isLE_derivedTensorProduct R (canonicalDerivedTensorProduct R) K L a b

end Stacks.DerivedTensor.RingedSite

end
