module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The quotient of the structure sheaf by a sheaf of ideals

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it and `I ⊆ O` a sheaf of ideals.
This file constructs `O/I` as a sheaf of commutative rings on `(C, J)`, together with the
quotient map `O ⟶ O/I`, the surjection `O/I ⟶ O/I'` attached to an inclusion `I ⊆ I'`, and the
tower `… ⟶ O/I³ ⟶ O/I² ⟶ O/I` of quotients by the powers of a sheaf of ideals.

## Main definitions

* `Stacks.Sites.quotientPresheaf`: the objectwise quotient `U ↦ O(U)/I(U)`, a presheaf of
  commutative rings.
* `Stacks.Sites.quotientRingSheaf`: the quotient `O/I`, a sheaf of commutative rings.
* `Stacks.Sites.toQuotientRingSheaf`: the quotient map `O ⟶ O/I`.
* `Stacks.Sites.quotientRingSheafMapOfLE`: the map `O/I ⟶ O/I'` attached to `I ⊆ I'`.
* `Stacks.Sites.adicQuotient` and `Stacks.Sites.adicQuotientMap`: the quotients `O/Iⁿ` by the
  powers of a sheaf of ideals and the maps `O/Iⁿ ⟶ O/Iᵐ` for `m ≤ n`.
* `Stacks.Sites.quotientRingedSite`: the ringed site obtained by replacing the structure sheaf
  of a ringed site by `O/I`.

## Main results

* `Stacks.Sites.toQuotientPresheaf_app_surjective` and
  `Stacks.Sites.ker_toQuotientPresheaf_app`: over every object of the site the objectwise
  quotient map is surjective with kernel the sections of `I`.
* `Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafMapOfLE` and
  `Stacks.Sites.toAdicQuotient_comp_adicQuotientMap`: the quotient maps are compatible with the
  comparisons between quotients.
* `Stacks.Sites.adicQuotient_one`: the first term of the tower is `O/I`.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ u

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The objectwise quotient of the structure sheaf by a sheaf of ideals, a presheaf of
commutative rings with `U ↦ O(U)/I(U)`. -/
noncomputable def quotientPresheaf (I : IdealSubsheaf O) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (O.obj.obj X ⧸ sectionIdeal I X)
  map {X Y} f := CommRingCat.ofHom
    (Ideal.quotientMap (sectionIdeal I Y) (O.obj.map f).hom
      fun _ h => map_mem_sectionIdeal I f h)
  map_id X := by
    ext a
    change Ideal.Quotient.mk (sectionIdeal I X) (O.obj.map (𝟙 X) a) =
      Ideal.Quotient.mk (sectionIdeal I X) a
    rw [O.obj.map_id]; rfl
  map_comp {X Y Z} f g := by
    ext a
    change Ideal.Quotient.mk (sectionIdeal I Z) (O.obj.map (f ≫ g) a) =
      Ideal.Quotient.mk (sectionIdeal I Z) (O.obj.map g (O.obj.map f a))
    rw [O.obj.map_comp]; rfl

/-- The objectwise quotient map `O(U) ⟶ O(U)/I(U)`. -/
noncomputable def toQuotientPresheaf (I : IdealSubsheaf O) : O.obj ⟶ quotientPresheaf I where
  app X := CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal I X))
  naturality {X Y} f := by ext; rfl

/-- The objectwise quotient map is surjective over every object of the site. -/
theorem toQuotientPresheaf_app_surjective (I : IdealSubsheaf O) (X : Cᵒᵖ) :
    Function.Surjective ((toQuotientPresheaf I).app X).hom :=
  Ideal.Quotient.mk_surjective

/-- The kernel of the objectwise quotient map over an object of the site is the ideal of
sections of `I` there. -/
@[simp]
theorem ker_toQuotientPresheaf_app (I : IdealSubsheaf O) (X : Cᵒᵖ) :
    RingHom.ker ((toQuotientPresheaf I).app X).hom = sectionIdeal I X :=
  Ideal.mk_ker

/-- The objectwise comparison `O/I ⟶ O/I'` attached to an inclusion `I ⊆ I'` of sheaves of
ideals. -/
noncomputable def quotientPresheafMapOfLE {I I' : IdealSubsheaf O} (h : I ≤ I') :
    quotientPresheaf I ⟶ quotientPresheaf I' where
  app X := CommRingCat.ofHom
    (Ideal.Quotient.factor (_root_.SheafOfModules.Submodule.le_iff.1 h X))
  naturality {X Y} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

/-- The objectwise quotient maps are compatible with the comparison attached to an inclusion of
sheaves of ideals. -/
@[simp]
theorem toQuotientPresheaf_comp_quotientPresheafMapOfLE {I I' : IdealSubsheaf O} (h : I ≤ I') :
    toQuotientPresheaf I ≫ quotientPresheafMapOfLE h = toQuotientPresheaf I' := by
  ext X a
  rfl

/-- The objectwise comparisons compose. -/
theorem quotientPresheafMapOfLE_comp {I I' I'' : IdealSubsheaf O} (h : I ≤ I') (h' : I' ≤ I'') :
    quotientPresheafMapOfLE h ≫ quotientPresheafMapOfLE h' =
      quotientPresheafMapOfLE (h.trans h') := by
  ext X : 2
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

section Sheafify

variable [HasWeakSheafify J CommRingCat.{u}]

/-- **The quotient `O/I` of a sheaf of commutative rings by a sheaf of ideals**, the
sheafification of the objectwise quotient. -/
noncomputable def quotientRingSheaf (I : IdealSubsheaf O) : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (quotientPresheaf I)

/-- The quotient map `O ⟶ O/I`, the objectwise quotient map followed by the comparison with the
sheafification. -/
noncomputable def toQuotientRingSheaf (I : IdealSubsheaf O) : O ⟶ quotientRingSheaf I :=
  ⟨toQuotientPresheaf I ≫ toSheafify J (quotientPresheaf I)⟩

/-- The comparison `O/I ⟶ O/I'` attached to an inclusion `I ⊆ I'` of sheaves of ideals. -/
noncomputable def quotientRingSheafMapOfLE {I I' : IdealSubsheaf O} (h : I ≤ I') :
    quotientRingSheaf I ⟶ quotientRingSheaf I' :=
  (presheafToSheaf J CommRingCat.{u}).map (quotientPresheafMapOfLE h)

/-- The quotient maps are compatible with the comparison attached to an inclusion of sheaves of
ideals. -/
@[simp]
theorem toQuotientRingSheaf_comp_quotientRingSheafMapOfLE {I I' : IdealSubsheaf O} (h : I ≤ I') :
    toQuotientRingSheaf I ≫ quotientRingSheafMapOfLE h = toQuotientRingSheaf I' := by
  apply Sheaf.hom_ext
  show (toQuotientPresheaf I ≫ toSheafify J (quotientPresheaf I)) ≫
      sheafifyMap J (quotientPresheafMapOfLE h) =
    toQuotientPresheaf I' ≫ toSheafify J (quotientPresheaf I')
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc,
    toQuotientPresheaf_comp_quotientPresheafMapOfLE]

/-- The comparisons compose. -/
theorem quotientRingSheafMapOfLE_comp {I I' I'' : IdealSubsheaf O} (h : I ≤ I')
    (h' : I' ≤ I'') :
    quotientRingSheafMapOfLE h ≫ quotientRingSheafMapOfLE h' =
      quotientRingSheafMapOfLE (h.trans h') :=
  ((presheafToSheaf J CommRingCat.{u}).map_comp _ _).symm.trans
    (congrArg (presheafToSheaf J CommRingCat.{u}).map (quotientPresheafMapOfLE_comp h h'))

/-- **The quotient `O/Iⁿ` by a power of a sheaf of ideals.** -/
noncomputable def adicQuotient (I : IdealSubsheaf O) (n : ℕ) : Sheaf J CommRingCat.{u} :=
  quotientRingSheaf (idealPow I n)

/-- The quotient map `O ⟶ O/Iⁿ`. -/
noncomputable def toAdicQuotient (I : IdealSubsheaf O) (n : ℕ) : O ⟶ adicQuotient I n :=
  toQuotientRingSheaf (idealPow I n)

/-- The map `O/Iⁿ ⟶ O/Iᵐ` of the tower of quotients by the powers of a sheaf of ideals, for
`m ≤ n`. -/
noncomputable def adicQuotientMap (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    adicQuotient I n ⟶ adicQuotient I m :=
  quotientRingSheafMapOfLE (idealPow_antitone I h)

/-- The quotient maps are compatible with the tower. -/
@[simp]
theorem toAdicQuotient_comp_adicQuotientMap (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    toAdicQuotient I n ≫ adicQuotientMap I h = toAdicQuotient I m :=
  toQuotientRingSheaf_comp_quotientRingSheafMapOfLE _

/-- The tower maps compose. -/
theorem adicQuotientMap_comp (I : IdealSubsheaf O) {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    adicQuotientMap I h' ≫ adicQuotientMap I h = adicQuotientMap I (h.trans h') :=
  quotientRingSheafMapOfLE_comp _ _

/-- The first term of the tower is `O/I`. -/
theorem adicQuotient_one (I : IdealSubsheaf O) : adicQuotient I 1 = quotientRingSheaf I := by
  rw [adicQuotient, idealPow_one]

/-- The ringed site with the same underlying site and the structure sheaf replaced by `O/I`. -/
noncomputable def quotientRingedSite (X : AlgebraicGeometry.RingedSite.{u₁, v₁, u})
    [HasWeakSheafify X.J CommRingCat.{u}]
    (I : letI := X.hasSheafCompose_forget₂_ringCat; IdealSubsheaf X.O) :
    AlgebraicGeometry.RingedSite.{u₁, v₁, u} :=
  letI := X.hasSheafCompose_forget₂_ringCat
  { C := X.C, J := X.J, O := quotientRingSheaf I }

/-- The underlying site of a quotient ringed site is unchanged. -/
@[simp]
theorem quotientRingedSite_J (X : AlgebraicGeometry.RingedSite.{u₁, v₁, u})
    [HasWeakSheafify X.J CommRingCat.{u}]
    (I : letI := X.hasSheafCompose_forget₂_ringCat; IdealSubsheaf X.O) :
    (quotientRingedSite X I).J = X.J :=
  rfl

/-- The structure sheaf of a quotient ringed site is the quotient sheaf of rings. -/
theorem quotientRingedSite_O (X : AlgebraicGeometry.RingedSite.{u₁, v₁, u})
    [HasWeakSheafify X.J CommRingCat.{u}]
    (I : letI := X.hasSheafCompose_forget₂_ringCat; IdealSubsheaf X.O) :
    (quotientRingedSite X I).O =
      letI := X.hasSheafCompose_forget₂_ringCat; quotientRingSheaf I :=
  rfl

end Sheafify

end Stacks.Sites

end
