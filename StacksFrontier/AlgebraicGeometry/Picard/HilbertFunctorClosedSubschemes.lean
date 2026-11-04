module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubobject
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf

/-!
# The Hilbert functor of points in terms of closed subschemes

Stacks Section 0B94 defines, for a morphism of schemes `X ⟶ S`, an integer `d ≥ 0` and a scheme `T`
over `S`,

`Hilb^d_{X/S}(T) = {Z ⊂ X_T closed subscheme such that Z → T is finite locally free of degree d}`,

and lets a morphism `T' ⟶ T` act by sending `Z` to its base change `Z_{T'} ⊂ X_{T'}`. That functor
is `Stacks.Hilbert.hilbertFunctorOfRank`, whose values `Stacks.Hilbert.HilbertFamily` record a
closed subscheme by its quasi-coherent ideal sheaf. This file describes these values as closed
subschemes of `X_T`, that is subobjects of `X_T` presented by a closed immersion, and identifies
the two descriptions.

## Main definitions

* `Stacks.Hilbert.hilbertSubobjects X T d` — the set `Hilb^d_{X/S}(T)`: the subobjects `Z` of `X_T`
  presented by a closed immersion `Z → X_T` for which `Z → T` is finite locally free of degree `d`.
* `Stacks.Hilbert.hilbertFamilyEquivHilbertSubobjects` — the bijection between degree-`d` Hilbert
  families over `T` and `hilbertSubobjects X T d`.
* `Stacks.Hilbert.hilbertScheme` — the scheme `\underline{Hilb}^d_{X/S}` representing the functor,
  when it is representable.

## Main results

* `Stacks.Hilbert.mk_mem_hilbertSubobjects_iff` — membership of the subobject presented by a
  monomorphism `Z → X_T` in `Hilb^d_{X/S}(T)` is exactly the condition of the section on that
  monomorphism: it is a closed immersion and `Z → T` is finite locally free of degree `d`.
* `Stacks.Hilbert.pullback_mem_hilbertSubobjects` — base change along `T' ⟶ T` carries
  `Hilb^d_{X/S}(T)` into `Hilb^d_{X/S}(T')`.
* `Stacks.Hilbert.hilbertFamilyEquivHilbertSubobjects_baseChange` and
  `Stacks.Hilbert.hilbertFamilyEquivHilbertSubobjects_map` — under the bijection, the action of
  `hilbertFunctorOfRank` on a morphism `T' ⟶ T` is base change of the closed subscheme.
* `Stacks.Hilbert.RepresentsHilbertFunctorOfRank.representableBy` — a representing scheme in the
  sense of `Stacks.Hilbert.RepresentsHilbertFunctorOfRank` represents `hilbertFunctorOfRank`.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- Finite local freeness of a given rank is invariant under precomposition with an isomorphism. -/
theorem isFiniteLocallyFreeOfRank_iso_hom_comp {A B Y : Scheme.{u}} (e : A ≅ B) (f : B ⟶ Y)
    (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (e.hom ≫ f) d :=
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_horiz_isIso (fst := e.hom) (snd := e.hom ≫ f) (f := f) (g := 𝟙 Y)
      ⟨by simp⟩)

/-- The set `Hilb^d_{X/S}(T)` of closed subschemes `Z ⊂ X_T`, that is subobjects of `X_T = X ×_S T`
presented by a closed immersion, such that `Z → T` is finite locally free of degree `d`. -/
@[stacks 0B94 "the set `Hilb^d_{X/S}(T)` of closed subschemes `Z ⊂ X_T` (closed immersions \
into `X_T` up to isomorphism over `X_T`) with `Z → T` finite locally free of degree `d`"]
def hilbertSubobjects (X T : Over S) (d : ℕ) :
    Set (Subobject ((Over.pullback T.hom).obj X).left) :=
  {Z | IsClosedImmersion Z.arrow ∧
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Z.arrow ≫ ((Over.pullback T.hom).obj X).hom) d}

/-- The subobject presented by a monomorphism `f : Z ⟶ X_T` lies in `Hilb^d_{X/S}(T)` exactly when
`f` is a closed immersion and `Z → T` is finite locally free of degree `d`: membership does not
depend on the chosen representative. -/
theorem mk_mem_hilbertSubobjects_iff {X T : Over S} {d : ℕ} {Z : Scheme.{u}}
    (f : Z ⟶ ((Over.pullback T.hom).obj X).left) [Mono f] :
    Subobject.mk f ∈ hilbertSubobjects X T d ↔
      IsClosedImmersion f ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f ≫ ((Over.pullback T.hom).obj X).hom) d := by
  have e₁ : (Subobject.mk f).arrow = (Subobject.underlyingIso f).hom ≫ f :=
    (Subobject.underlyingIso_hom_comp_eq_mk f).symm
  have e₂ : f = (Subobject.underlyingIso f).inv ≫ (Subobject.mk f).arrow := by
    rw [e₁, Iso.inv_hom_id_assoc]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨?_, ?_⟩⟩
  · rw [e₂]; infer_instance
  · rw [e₂, Category.assoc]
    exact isFiniteLocallyFreeOfRank_iso_hom_comp (Subobject.underlyingIso f).symm _ d
  · rw [e₁]; infer_instance
  · rw [e₁, Category.assoc]
    exact isFiniteLocallyFreeOfRank_iso_hom_comp _ _ d

/-- The closed subscheme cut out by a degree-`d` Hilbert family lies in `Hilb^d_{X/S}(T)`. -/
theorem HilbertFamily.mk_subschemeι_mem {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d) :
    Subobject.mk Z.ideal.subschemeι ∈ hilbertSubobjects X T d :=
  (mk_mem_hilbertSubobjects_iff _).mpr ⟨inferInstance, Z.isFiniteLocallyFreeOfRank⟩

/-- The degree-`d` Hilbert family cut out by the ideal sheaf of a member of `Hilb^d_{X/S}(T)`. -/
def HilbertFamily.ofHilbertSubobject {X T : Over S} {d : ℕ}
    (Z : hilbertSubobjects X T d) : HilbertFamily X T d where
  ideal := Z.1.arrow.ker
  isFiniteLocallyFreeOfRank := by
    have := Z.2.1
    have := Z.2.2
    have h : Z.1.arrow.ker.subschemeι = inv Z.1.arrow.toImage ≫ Z.1.arrow := by
      rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
    rw [h, Category.assoc]
    exact isFiniteLocallyFreeOfRank_iso_hom_comp (asIso Z.1.arrow.toImage).symm _ d

/-- The degree-`d` Hilbert families in `X` over `T`, which record a closed subscheme of `X_T` by
its ideal sheaf, are in bijection with the set `Hilb^d_{X/S}(T)` of closed subschemes `Z ⊂ X_T`
with `Z → T` finite locally free of degree `d`. A family is sent to the closed subscheme it cuts
out, and a closed subscheme to its ideal sheaf. -/
@[stacks 0B94 "the values of `Stacks.Hilbert.hilbertFunctorOfRank` are the sets \
`Hilb^d_{X/S}(T)` of closed subschemes of the section: a bijection with \
`Stacks.Hilbert.hilbertSubobjects`"]
def hilbertFamilyEquivHilbertSubobjects (X T : Over S) (d : ℕ) :
    HilbertFamily X T d ≃ hilbertSubobjects X T d where
  toFun Z := ⟨Subobject.mk Z.ideal.subschemeι, Z.mk_subschemeι_mem⟩
  invFun Z := HilbertFamily.ofHilbertSubobject Z
  left_inv Z := HilbertFamily.ext (by
    change (Subobject.mk Z.ideal.subschemeι).arrow.ker = Z.ideal
    rw [Scheme.Hom.ker_subobject_mk_arrow, Scheme.IdealSheafData.ker_subschemeι])
  right_inv Z := by
    refine Subtype.ext ?_
    change Subobject.mk Z.1.arrow.ker.subschemeι = Z.1
    have := Z.2.1
    conv_rhs => rw [← Subobject.mk_arrow Z.1]
    exact Subobject.mk_eq_mk_of_comm _ _ (asIso Z.1.arrow.toImage).symm
      (by rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι])

/-- The closed subscheme attached to a Hilbert family is the one its ideal sheaf cuts out. -/
@[simp]
theorem hilbertFamilyEquivHilbertSubobjects_apply_coe {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) :
    (hilbertFamilyEquivHilbertSubobjects X T d Z : Subobject _) =
      Subobject.mk Z.ideal.subschemeι :=
  rfl

/-- Base change of Hilbert families is base change of the closed subschemes they cut out: the
closed subscheme of `X_{T'}` attached to the base change of `Z` along `g : T' ⟶ T` is the pullback
of the closed subscheme attached to `Z` along `X_{T'} ⟶ X_T`. -/
theorem hilbertFamilyEquivHilbertSubobjects_baseChange (X : Over S) {T' T : Over S} {d : ℕ}
    (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    (hilbertFamilyEquivHilbertSubobjects X T' d (baseChange X g Z) : Subobject _) =
      (Subobject.pullback (familyBaseChangeMap X g)).obj
        (hilbertFamilyEquivHilbertSubobjects X T d Z) := by
  rw [hilbertFamilyEquivHilbertSubobjects_apply_coe, hilbertFamilyEquivHilbertSubobjects_apply_coe,
    Scheme.IdealSheafData.subobject_pullback_mk_subschemeι, baseChange_ideal]

/-- For a morphism `T' ⟶ T` of schemes over `S` and a `Z ∈ Hilb^d_{X/S}(T)`, the base change
`Z_{T'} ⊂ X_{T'}`, the pullback of `Z` along `X_{T'} ⟶ X_T`, is an element of
`Hilb^d_{X/S}(T')`. -/
@[stacks 0B94 "for `T' ⟶ T` over `S` and `Z ∈ Hilb^d_{X/S}(T)`, the base change \
`Z_{T'} ⊂ X_{T'}` lies in `Hilb^d_{X/S}(T')`"]
theorem pullback_mem_hilbertSubobjects (X : Over S) {T' T : Over S} {d : ℕ} (g : T' ⟶ T)
    {Z : Subobject ((Over.pullback T.hom).obj X).left} (hZ : Z ∈ hilbertSubobjects X T d) :
    (Subobject.pullback (familyBaseChangeMap X g)).obj Z ∈ hilbertSubobjects X T' d := by
  obtain ⟨W, hW⟩ := (hilbertFamilyEquivHilbertSubobjects X T d).surjective ⟨Z, hZ⟩
  rw [show Z = hilbertFamilyEquivHilbertSubobjects X T d W from (congrArg Subtype.val hW).symm,
    ← hilbertFamilyEquivHilbertSubobjects_baseChange]
  exact Subtype.property _

/-- The functor `Hilb^d_{X/S} : (Sch/S)ᵒᵖ ⥤ Sets` acts on a morphism `T' ⟶ T` by base change of the
closed subscheme: under the identification of its values with `Hilb^d_{X/S}(T)`, the image of `Z`
is the pullback of `Z` along `X_{T'} ⟶ X_T`. -/
@[stacks 0B94 "the functor `Hilb^d_{X/S}` acts on morphisms `T' ⟶ T` by base change of the \
closed subscheme `Z ⊂ X_T` to `Z_{T'} ⊂ X_{T'}`"]
theorem hilbertFamilyEquivHilbertSubobjects_map (X : Over S) (d : ℕ) {T' T : Over S}
    (g : T' ⟶ T) (Z : (hilbertFunctorOfRank X d).obj (op T)) :
    (hilbertFamilyEquivHilbertSubobjects X T' d ((hilbertFunctorOfRank X d).map g.op Z) :
        Subobject _) =
      (Subobject.pullback (familyBaseChangeMap X g)).obj
        (hilbertFamilyEquivHilbertSubobjects X T d Z) :=
  hilbertFamilyEquivHilbertSubobjects_baseChange X g Z

/-- A scheme representing the degree-`d` Hilbert functor in the sense of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank` represents `hilbertFunctorOfRank X d`. -/
def RepresentsHilbertFunctorOfRank.representableBy {X H : Over S} {d : ℕ}
    (h : RepresentsHilbertFunctorOfRank X H d) : (hilbertFunctorOfRank X d).RepresentableBy H where
  homEquiv := h.family
  homEquiv_comp g f := HilbertFamily.ext (h.naturality g f)

/-- The scheme `\underline{Hilb}^d_{X/S}` over `S` representing the degree-`d` Hilbert functor,
when that functor is representable by a scheme. -/
@[stacks 0B94 "the notation `\\underline{Hilb}^d_{X/S}` for the representing scheme"]
abbrev hilbertScheme (X : Over S) (d : ℕ) [(hilbertFunctorOfRank X d).IsRepresentable] :
    Over S :=
  (hilbertFunctorOfRank X d).reprX

end Stacks.Hilbert

end
