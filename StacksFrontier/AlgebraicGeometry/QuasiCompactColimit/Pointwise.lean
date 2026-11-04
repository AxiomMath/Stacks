module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising a filtered colimit of commutative rings elementwise

A cocone over a filtered diagram of commutative rings is colimiting exactly when it is so on
underlying sets, that is when its components are jointly surjective and two elements with the
same image already agree at a later index. This file proves that these two elementwise
conditions imply `CategoryTheory.Limits.IsColimit`.

Together with `Stacks.QuasiCompactColimit.isColimitOfBasis` this turns the affine content of
Stacks Tag 05JT -- that the sections of an algebra over an affine open are the union of the
sections of its finite type subalgebras -- into the sheaf-level colimit assertion.

## Main definitions

* `Stacks.QuasiCompactColimit.isColimitOfFaithful`: the dual of
  `CategoryTheory.Limits.IsLimit.ofFaithful`.
* `Stacks.QuasiCompactColimit.descFun` and `Stacks.QuasiCompactColimit.descRingHom`: the map of
  underlying sets determined by a second cocone, and the ring morphism it underlies.

## Main results

* `Stacks.QuasiCompactColimit.exists_rep₂`: two elements of the vertex come from one index.
* `Stacks.QuasiCompactColimit.isColimitForget`: the cocone of underlying sets is colimiting.
* `Stacks.QuasiCompactColimit.isColimitOfJointlySurjective`: a cocone over a filtered diagram of
  commutative rings is colimiting as soon as its components are jointly surjective and injective
  up to a later index.
* `Stacks.QuasiCompactColimit.isColimitOfInjective`: the same with injective components, where
  the second condition is automatic.

## Implementation notes

The results are not obtained by reflection along the forgetful functor:
`CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms` requires
`CategoryTheory.Limits.HasColimit` for the diagram, and `CommRingCat.{u}` has colimits only of
shapes small relative to `u`. The index category of Tag 05JT is a category of subobjects of a
sheaf of rings on a scheme, and
`CategoryTheory.Limits.HasColimitsOfShape (FiniteTypeSubalgebra A) CommRingCat.{u}` does not
synthesize, so that route is unavailable there. The statements here carry no size hypothesis:
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'` is universe polymorphic and needs no
colimits to exist, and the ring structure on the descended map is supplied by `exists_rep₂`.

`Stacks.QuasiCompactColimit.descRingHom` uses `CategoryTheory.ConcreteCategory.ofHom` rather
than `CommRingCat.ofHom`: the latter is stated for objects of the form `CommRingCat.of R` and
the vertices here are arbitrary objects.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₃ u₃ v u v' u'

namespace Stacks.QuasiCompactColimit

section Faithful

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C] {F : J ⥤ C} {t : Cocone F}
  {D : Type u₃} [Category.{v₃} D]

/-- The dual of `CategoryTheory.Limits.IsLimit.ofFaithful`: a cocone is colimiting as soon as a
faithful functor carries it to a colimiting cocone and the factorisations it needs are already
available in the source category. -/
def isColimitOfFaithful (G : C ⥤ D) [G.Faithful]
    (ht : IsColimit (G.mapCocone t)) (desc : ∀ s : Cocone F, t.pt ⟶ s.pt)
    (h : ∀ s, G.map (desc s) = ht.desc (G.mapCocone s)) : IsColimit t where
  desc := desc
  fac s j := G.map_injective <| by
    rw [G.map_comp, h]
    exact ht.fac (G.mapCocone s) j
  uniq s m hm := G.map_injective <| by
    rw [h]
    refine ht.uniq (G.mapCocone s) (G.map m) fun j => ?_
    rw [Functor.mapCocone_ι_app, Functor.mapCocone_ι_app, ← G.map_comp, hm j]

end Faithful

section Rings

variable {K : Type u'} [Category.{v'} K] [IsFiltered K] {F : K ⥤ CommRingCat.{u}}

/-- Two elements of the vertex of a cocone whose components are jointly surjective come from a
single index, the diagram being filtered. -/
theorem exists_rep₂ (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (k : K) (y : F.obj k), c.ι.app k y = x) (x y : c.pt) :
    ∃ (k : K) (a : F.obj k) (b : F.obj k), c.ι.app k a = x ∧ c.ι.app k b = y := by
  obtain ⟨k, a, ha⟩ := hsurj x
  obtain ⟨l, b, hb⟩ := hsurj y
  refine ⟨IsFiltered.max k l, F.map (IsFiltered.leftToMax k l) a,
    F.map (IsFiltered.rightToMax k l) b, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, c.w (IsFiltered.leftToMax k l), ha]
  · rw [← ConcreteCategory.comp_apply, c.w (IsFiltered.rightToMax k l), hb]

variable (c : Cocone F)

/-- The cocone of underlying sets of a cocone whose components are jointly surjective and
injective up to a later index is colimiting. -/
def isColimitForget
    (hsurj : ∀ x : c.pt, ∃ (k : K) (y : F.obj k), c.ι.app k y = x)
    (hinj : ∀ (k : K) (x y : F.obj k), c.ι.app k x = c.ι.app k y →
      ∃ (l : K) (f : k ⟶ l), F.map f x = F.map f y) :
    IsColimit ((forget CommRingCat.{u}).mapCocone c) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun x => by obtain ⟨k, y, hy⟩ := hsurj x; exact ⟨k, y, hy.symm⟩)
    fun k x y h => hinj k x y h

variable (hT : IsColimit ((forget CommRingCat.{u}).mapCocone c))

/-- The map of underlying sets out of the vertex of `c` determined by a second cocone. -/
def descFun (s : Cocone F) : ToType c.pt → ToType s.pt :=
  fun x => hT.desc ((forget CommRingCat.{u}).mapCocone s) x

omit [IsFiltered K] in
/-- The map `descFun c hT s` sends the image of `a : F.obj k` in the vertex of `c` to its image in
the vertex of `s`. -/
@[simp]
theorem descFun_ι (s : Cocone F) (k : K) (a : F.obj k) :
    descFun c hT s (c.ι.app k a) = s.ι.app k a := by
  have h := ConcreteCategory.congr_hom (hT.fac ((forget CommRingCat.{u}).mapCocone s) k) a
  simpa [descFun, ConcreteCategory.comp_apply] using h

variable (hsurj : ∀ x : c.pt, ∃ (k : K) (y : F.obj k), c.ι.app k y = x)

/-- The morphism of commutative rings out of the vertex of `c` determined by a second cocone `s`,
whose underlying map is `descFun c hT s`. -/
def descRingHom (s : Cocone F) : c.pt ⟶ s.pt :=
  ConcreteCategory.ofHom (C := CommRingCat)
    { toFun := descFun c hT s
      map_one' := by
        obtain ⟨k⟩ := IsFiltered.nonempty (C := K)
        have h1 : (1 : ToType c.pt) = c.ι.app k 1 := ((c.ι.app k).hom.map_one).symm
        rw [h1, descFun_ι]
        exact (s.ι.app k).hom.map_one
      map_mul' := fun x y => by
        obtain ⟨k, a, b, hax, hby⟩ := exists_rep₂ c hsurj x y
        subst hax
        subst hby
        have hmul : c.ι.app k a * c.ι.app k b = c.ι.app k (a * b) :=
          ((c.ι.app k).hom.map_mul a b).symm
        rw [hmul]
        simp only [descFun_ι]
        exact (s.ι.app k).hom.map_mul a b
      map_zero' := by
        obtain ⟨k⟩ := IsFiltered.nonempty (C := K)
        have h0 : (0 : ToType c.pt) = c.ι.app k 0 := ((c.ι.app k).hom.map_zero).symm
        rw [h0, descFun_ι]
        exact (s.ι.app k).hom.map_zero
      map_add' := fun x y => by
        obtain ⟨k, a, b, hax, hby⟩ := exists_rep₂ c hsurj x y
        subst hax
        subst hby
        have hadd : c.ι.app k a + c.ι.app k b = c.ι.app k (a + b) :=
          ((c.ι.app k).hom.map_add a b).symm
        rw [hadd]
        simp only [descFun_ι]
        exact (s.ι.app k).hom.map_add a b }

/-- **Recognising a filtered colimit of commutative rings elementwise.**  A cocone over a
filtered diagram of commutative rings is colimiting as soon as its components are jointly
surjective and two elements with the same image already agree at a later index. -/
def isColimitOfJointlySurjective
    (hinj : ∀ (k : K) (x y : F.obj k), c.ι.app k x = c.ι.app k y →
      ∃ (l : K) (f : k ⟶ l), F.map f x = F.map f y) :
    IsColimit c :=
  isColimitOfFaithful (forget CommRingCat.{u}) (isColimitForget c hsurj hinj)
    (descRingHom c (isColimitForget c hsurj hinj) hsurj) fun _ => rfl

/-- **A filtered union of subrings is their colimit.**  A cocone over a filtered diagram of
commutative rings whose components are injective is colimiting as soon as they are jointly
surjective. -/
def isColimitOfInjective (hmono : ∀ k : K, Function.Injective (c.ι.app k)) : IsColimit c :=
  isColimitOfJointlySurjective c hsurj fun k x y h => ⟨k, 𝟙 k, by rw [hmono k h]⟩

end Rings

end Stacks.QuasiCompactColimit
