module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpenRepresentable

/-!
# The Hilbert functor over an open of the base

Let `X` be a scheme over `S`, let `V ⊆ S` be an open and let `d` be a natural number. The
degree-`d` Hilbert families in `X` over those `S`-schemes `T` whose structure morphism lands in
`V` form a subfunctor `Stacks.Hilbert.overOpen X d V` of the degree-`d` Hilbert functor of `X`.
This file proves that these subfunctors are the input the gluing criterion of Stacks 01JJ needs
for the reduction to an affine base in the proof of Stacks Tag 0B9A, which the source leaves to
the reader ("Details omitted"):

* each `overOpen X d V` is an open subfunctor;
* the subfunctors attached to an open cover of `S` contain every field-valued point;
* `overOpen X d V` is represented by any scheme over `V` representing the degree-`d` Hilbert
  functor of `X ×_S V` over `V`, regarded as a scheme over `S`.

## Main definitions

* `Stacks.Hilbert.overOpen` — the subfunctor of families over bases mapping into `V`.
* `Stacks.Hilbert.baseRestrict` — the scheme `X ×_S V` over `V`.
* `Stacks.Hilbert.liftToOpen` — an `S`-scheme mapping into `V`, regarded as a scheme over `V`.
* `Stacks.Hilbert.familyLiftEquiv` — the families in `X ×_S V` over such a scheme are the
  families in `X` over it.

## Main results

* `Stacks.Hilbert.isOpenHilbertSubfunctor_overOpen` — `overOpen X d V` is open.
* `Stacks.Hilbert.exists_mem_overOpen_of_specField` — the subfunctors attached to a cover of `S`
  cover the field-valued points.
* `Stacks.Hilbert.overOpenRepresentableBy` — representability of `overOpen X d V`.

## Implementation notes

An `S`-scheme `T` whose structure morphism lands in `V` factors uniquely through the open
immersion `V ⟶ S`, by `AlgebraicGeometry.IsOpenImmersion.lift`; this gives the scheme over `V`
called `liftToOpen`. The ambient scheme `(X ×_S V) ×_V T` of its families is identified with
`X ×_S T` by pasting the two cartesian squares, and families are transported along that
isomorphism by pulling back ideal sheaves. Morphisms over `S` into a scheme over `V` regarded
over `S` are morphisms over `V`, because `V ⟶ S` is a monomorphism.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-! ### The subfunctor, its openness and the covering property -/

/-- The subfunctor of the degree-`d` Hilbert functor of `X` consisting of the families over the
`S`-schemes whose structure morphism lands in an open `V ⊆ S`. -/
def overOpen (X : Over S) (d : ℕ) (V : S.Opens) : Subfunctor (hilbertFunctorOfRank X d) where
  obj T := {_Z | Set.range T.unop.hom ⊆ V}
  map g _ h := by
    rintro _ ⟨t, rfl⟩
    rw [← Over.w g.unop, Scheme.Hom.comp_apply]
    exact h ⟨_, rfl⟩

/-- A family over `T` lies in `overOpen X d V` exactly when the structure morphism of `T` lands in
`V`. -/
@[simp]
theorem mem_overOpen_obj {X : Over S} {d : ℕ} {V : S.Opens} {T : (Over S)ᵒᵖ}
    {Z : HilbertFamily X T.unop d} : Z ∈ (overOpen X d V).obj T ↔ Set.range T.unop.hom ⊆ V :=
  Iff.rfl

/-- The subfunctor `overOpen X d V` is open: a base change along `g : T' ⟶ T` lies in it exactly
when `g` lands in the preimage of `V` in `T`. -/
theorem isOpenHilbertSubfunctor_overOpen (X : Over S) (d : ℕ) (V : S.Opens) :
    IsOpenHilbertSubfunctor (overOpen X d V) := by
  intro T Z
  refine ⟨T.hom ⁻¹ᵁ V, fun T' g => ?_⟩
  change Set.range T'.hom ⊆ V ↔ _
  rw [← Over.w g]
  constructor <;> rintro h _ ⟨t, rfl⟩ <;> exact h ⟨t, rfl⟩

/-- The subfunctors `overOpen X d (V i)` attached to a cover of `S` by opens `V i` contain every
degree-`d` Hilbert family over the spectrum of a field. -/
theorem exists_mem_overOpen_of_specField (X : Over S) (d : ℕ) {ι : Type*} (V : ι → S.Opens)
    (hV : ∀ s : S, ∃ i, s ∈ V i) (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S)
    (Z : HilbertFamily X (Over.mk g) d) : ∃ i, Z ∈ (overOpen X d (V i)).obj (op (Over.mk g)) := by
  have : Subsingleton (Spec (CommRingCat.of k) : Type u) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k) : Type u) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨i, hi⟩ := hV (g x)
  refine ⟨i, ?_⟩
  rintro _ ⟨y, rfl⟩
  change g y ∈ V i
  rwa [Subsingleton.elim (α := (Spec (CommRingCat.of k) : Type u)) y x]

/-! ### Schemes over an open of the base -/

/-- The scheme `X ×_S V` over an open `V ⊆ S`. -/
abbrev baseRestrict (X : Over S) (V : S.Opens) : Over V.toScheme :=
  (Over.pullback V.ι).obj X

/-- An `S`-scheme whose structure morphism lands in an open `V ⊆ S`, as a scheme over `V`. -/
def liftToOpen {V : S.Opens} (T : Over S) (h : Set.range T.hom ⊆ V) : Over V.toScheme :=
  Over.mk (IsOpenImmersion.lift V.ι T.hom (by rwa [Scheme.Opens.range_ι]))

/-- The underlying scheme of `liftToOpen T h` is that of `T`. -/
@[simp]
theorem liftToOpen_left {V : S.Opens} (T : Over S) (h : Set.range T.hom ⊆ V) :
    (liftToOpen T h).left = T.left :=
  rfl

/-- The structure morphism of `liftToOpen T h` followed by `V ⟶ S` is the structure morphism of
`T`. -/
@[reassoc (attr := simp)]
theorem liftToOpen_hom_ι {V : S.Opens} (T : Over S) (h : Set.range T.hom ⊆ V) :
    (liftToOpen T h).hom ≫ V.ι = T.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The structure morphism of an `S`-scheme with a morphism into a scheme over `V` lands in
`V`. -/
theorem range_subset_of_hom {V : S.Opens} {H : Over V.toScheme} {T : Over S}
    (a : T ⟶ (Over.map V.ι).obj H) : Set.range T.hom ⊆ V := by
  rintro _ ⟨t, rfl⟩
  rw [← Over.w a, Over.map_obj_hom, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (Scheme.Opens.range_ι V).subset ⟨_, rfl⟩

/-- A morphism of `S`-schemes mapping into `V`, as a morphism of schemes over `V`. -/
def liftToOpenMap {V : S.Opens} {T' T : Over S} (f : T' ⟶ T) (h' : Set.range T'.hom ⊆ V)
    (h : Set.range T.hom ⊆ V) : liftToOpen T' h' ⟶ liftToOpen T h :=
  Over.homMk f.left (by
    change f.left ≫ IsOpenImmersion.lift V.ι T.hom _ = IsOpenImmersion.lift V.ι T'.hom _
    exact IsOpenImmersion.lift_uniq _ _ _ _
      ((Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (liftToOpen_hom_ι T h)).trans
        (Over.w f))))

/-- Morphisms over `S` into a scheme over `V` regarded over `S` are morphisms over `V`. -/
def homLiftEquiv {V : S.Opens} {H : Over V.toScheme} (T : Over S) (h : Set.range T.hom ⊆ V) :
    (T ⟶ (Over.map V.ι).obj H) ≃ (liftToOpen T h ⟶ H) where
  toFun a := Over.homMk a.left (by
    change a.left ≫ H.hom = IsOpenImmersion.lift V.ι T.hom _
    exact IsOpenImmersion.lift_uniq _ _ _ _ ((Category.assoc _ _ _).trans (by
      simpa using Over.w a)))
  invFun b := Over.homMk b.left (by
    change b.left ≫ H.hom ≫ V.ι = T.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ V.ι) (Over.w b)).trans (liftToOpen_hom_ι T h)))
  left_inv a := Over.OverMorphism.ext rfl
  right_inv b := Over.OverMorphism.ext rfl

/-- The bijection `homLiftEquiv` is compatible with precomposition by a morphism `f : T' ⟶ T`. -/
theorem homLiftEquiv_comp {V : S.Opens} {H : Over V.toScheme} {T' T : Over S} (f : T' ⟶ T)
    (a : T ⟶ (Over.map V.ι).obj H) (h' : Set.range T'.hom ⊆ V) (h : Set.range T.hom ⊆ V) :
    homLiftEquiv T' h' (f ≫ a) = liftToOpenMap f h' h ≫ homLiftEquiv T h a :=
  Over.OverMorphism.ext rfl

/-! ### Transport of families -/

/-- The ambient scheme `(X ×_S V) ×_V T` of the families over `T` regarded over `V` is the
fibre product `X ×_S T`. -/
theorem isPullback_liftToOpen (X : Over S) {V : S.Opens} (T : Over S) (h : Set.range T.hom ⊆ V) :
    IsPullback (familyProjection (baseRestrict X V) (liftToOpen T h) ≫ pullback.fst X.hom V.ι)
      ((Over.pullback (liftToOpen T h).hom).obj (baseRestrict X V)).hom X.hom T.hom := by
  have := (IsPullback.of_hasPullback (pullback.snd X.hom V.ι) (liftToOpen T h).hom).paste_horiz
    (IsPullback.of_hasPullback X.hom V.ι)
  rwa [liftToOpen_hom_ι] at this

/-- The isomorphism `(X ×_S V) ×_V T ≅ X ×_S T`. -/
def ambientLiftIso (X : Over S) {V : S.Opens} (T : Over S) (h : Set.range T.hom ⊆ V) :
    ((Over.pullback (liftToOpen T h).hom).obj (baseRestrict X V)).left ≅
      ((Over.pullback T.hom).obj X).left :=
  (isPullback_liftToOpen X T h).isoPullback

/-- The isomorphism `(X ×_S V) ×_V T ≅ X ×_S T` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem ambientLiftIso_hom_hom (X : Over S) {V : S.Opens} (T : Over S)
    (h : Set.range T.hom ⊆ V) :
    (ambientLiftIso X T h).hom ≫ ((Over.pullback T.hom).obj X).hom =
      ((Over.pullback (liftToOpen T h).hom).obj (baseRestrict X V)).hom :=
  (isPullback_liftToOpen X T h).isoPullback_hom_snd

/-- The isomorphism `(X ×_S V) ×_V T ≅ X ×_S T` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem ambientLiftIso_hom_familyProjection (X : Over S) {V : S.Opens} (T : Over S)
    (h : Set.range T.hom ⊆ V) :
    (ambientLiftIso X T h).hom ≫ familyProjection X T =
      familyProjection (baseRestrict X V) (liftToOpen T h) ≫ pullback.fst X.hom V.ι :=
  (isPullback_liftToOpen X T h).isoPullback_hom_fst

/-- The isomorphisms `(X ×_S V) ×_V T ≅ X ×_S T` commute with base change. -/
theorem familyBaseChangeMap_ambientLiftIso (X : Over S) {V : S.Opens} {T' T : Over S}
    (f : T' ⟶ T) (h' : Set.range T'.hom ⊆ V) (h : Set.range T.hom ⊆ V) :
    familyBaseChangeMap (baseRestrict X V) (liftToOpenMap f h' h) ≫ (ambientLiftIso X T h).hom =
      (ambientLiftIso X T' h').hom ≫ familyBaseChangeMap X f := by
  refine pullback.hom_ext ?_ ?_
  · change _ ≫ _ ≫ familyProjection X T = _ ≫ _ ≫ familyProjection X T
    rw [ambientLiftIso_hom_familyProjection, ← Category.assoc,
      familyBaseChangeMap_comp_familyProjection, familyBaseChangeMap_comp_familyProjection,
      ambientLiftIso_hom_familyProjection]
  · change _ ≫ _ ≫ ((Over.pullback T.hom).obj X).hom = _ ≫ _ ≫ ((Over.pullback T.hom).obj X).hom
    rw [ambientLiftIso_hom_hom, (isPullback_familyBaseChangeMap X f).w,
      ambientLiftIso_hom_hom_assoc]
    exact (isPullback_familyBaseChangeMap (baseRestrict X V) (liftToOpenMap f h' h)).w

/-- Pulling back an ideal sheaf along an isomorphism over `T` preserves finite local freeness of
rank `d` of the closed subscheme it cuts out. -/
theorem isFiniteLocallyFreeOfRank_comap_iso {P P' T : Scheme.{u}} (e : P' ≅ P)
    {p : P ⟶ T} {p' : P' ⟶ T} (he : e.hom ≫ p = p') (I : P.IdealSheafData) {d : ℕ}
    (hI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ p) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.comap e.hom).subschemeι ≫ p') d := by
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp
    (I.comapIso e.hom ≪≫ asIso (pullback.snd e.hom I.subschemeι)) _ hI
  rwa [Iso.trans_hom, asIso_hom, Category.assoc, ← pullback.condition_assoc,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc, he] at h

variable {X : Over S} {d : ℕ} {V : S.Opens}

/-- The degree-`d` Hilbert families in `X ×_S V` over an `S`-scheme `T` mapping into `V`,
regarded over `V`, are the degree-`d` Hilbert families in `X` over `T`. -/
def familyLiftEquiv (T : Over S) (h : Set.range T.hom ⊆ V) :
    HilbertFamily (baseRestrict X V) (liftToOpen T h) d ≃ HilbertFamily X T d where
  toFun W := ⟨W.ideal.comap (ambientLiftIso X T h).inv,
    isFiniteLocallyFreeOfRank_comap_iso (ambientLiftIso X T h).symm
      ((Iso.inv_comp_eq _).mpr (ambientLiftIso_hom_hom X T h).symm) _
      W.isFiniteLocallyFreeOfRank⟩
  invFun Z := ⟨Z.ideal.comap (ambientLiftIso X T h).hom,
    isFiniteLocallyFreeOfRank_comap_iso (ambientLiftIso X T h) (ambientLiftIso_hom_hom X T h) _
      Z.isFiniteLocallyFreeOfRank⟩
  left_inv W := HilbertFamily.ext (by
    simp only [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id])
  right_inv Z := HilbertFamily.ext (by
    simp only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id])

/-- The ideal sheaf of the family `familyLiftEquiv T h W` is the pullback of that of `W` along the
inverse of `ambientLiftIso X T h`. -/
theorem familyLiftEquiv_ideal (T : Over S) (h : Set.range T.hom ⊆ V)
    (W : HilbertFamily (baseRestrict X V) (liftToOpen T h) d) :
    (familyLiftEquiv T h W).ideal = W.ideal.comap (ambientLiftIso X T h).inv :=
  rfl

/-- The transport of families commutes with base change. -/
theorem familyLiftEquiv_baseChange {T' T : Over S} (f : T' ⟶ T) (h' : Set.range T'.hom ⊆ V)
    (h : Set.range T.hom ⊆ V) (W : HilbertFamily (baseRestrict X V) (liftToOpen T h) d) :
    familyLiftEquiv T' h' (baseChange (baseRestrict X V) (liftToOpenMap f h' h) W) =
      baseChange X f (familyLiftEquiv T h W) := by
  refine HilbertFamily.ext ?_
  simp only [familyLiftEquiv_ideal, baseChange_ideal, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← familyBaseChangeMap_ambientLiftIso, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The subfunctor `overOpen X d V` is representable** by any scheme over `V` representing the
degree-`d` Hilbert functor of `X ×_S V` over `V`, regarded as a scheme over `S`. -/
def overOpenRepresentableBy {H : Over V.toScheme}
    (hH : (hilbertFunctorOfRank (baseRestrict X V) d).RepresentableBy H) :
    (overOpen X d V).toFunctor.RepresentableBy ((Over.map V.ι).obj H) where
  homEquiv {T} :=
    { toFun a := ⟨familyLiftEquiv T (range_subset_of_hom a)
        (hH.homEquiv (homLiftEquiv T (range_subset_of_hom a) a)), range_subset_of_hom a⟩
      invFun Z := (homLiftEquiv T Z.2).symm (hH.homEquiv.symm ((familyLiftEquiv T Z.2).symm Z.1))
      left_inv a := by
        have h := range_subset_of_hom a
        exact (congrArg (homLiftEquiv T h).symm ((congrArg hH.homEquiv.symm
          ((familyLiftEquiv T h).symm_apply_apply _)).trans
            (hH.homEquiv.symm_apply_apply _))).trans ((homLiftEquiv T h).symm_apply_apply a)
      right_inv Z := Subtype.ext ((congrArg (familyLiftEquiv T Z.2)
        (hH.homEquiv.apply_symm_apply _)).trans ((familyLiftEquiv T Z.2).apply_symm_apply _)) }
  homEquiv_comp {T' T} f a := by
    refine Subtype.ext ?_
    have e₁ := homLiftEquiv_comp f a (range_subset_of_hom (f ≫ a)) (range_subset_of_hom a)
    have e₂ := hH.homEquiv_comp (liftToOpenMap f (range_subset_of_hom (f ≫ a))
      (range_subset_of_hom a)) (homLiftEquiv T (range_subset_of_hom a) a)
    exact (congrArg (fun b => familyLiftEquiv T' (range_subset_of_hom (f ≫ a)) (hH.homEquiv b))
      e₁).trans ((congrArg (familyLiftEquiv T' (range_subset_of_hom (f ≫ a))) e₂).trans
        (familyLiftEquiv_baseChange f _ _ _))

end Stacks.Hilbert

end
