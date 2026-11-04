module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SchemeToSpaceSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Affine schemes over an object of the big fppf site of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `V`
an object of `(Spaces/X)_fppf`. An *affine scheme over `V`* is an affine scheme `W` of the chosen
big fppf site of schemes together with a morphism from the algebraic space it represents to the
algebraic space underlying `V`. These form a category, fully faithfully embedded in the slice
`(Spaces/X)_fppf/V`, and the embedding is a dense subsite: every object of the slice is covered by
affine schemes.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver`: the affine schemes over `V`.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.toSlice`: the embedding into the slice.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.topology`: the induced topology.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.toSlice_isCoverDense`: the affine schemes
  over `V` cover every object of the slice.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.isTerminalOfIso`: an affine scheme whose
  represented space is identified with `V` is a terminal affine scheme over `V`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The inclusion of schemes into algebraic spaces is full. -/
instance schemeSpaceFunctor_full :
    (schemeSpaceFunctor T.schemeSite S T.scheme_mem).Full where
  map_surjective f :=
    ⟨yoneda.preimage f.hom, ObjectProperty.hom_ext _ (yoneda.map_preimage _)⟩

/-- The inclusion of schemes into algebraic spaces is faithful. -/
instance schemeSpaceFunctor_faithful :
    (schemeSpaceFunctor T.schemeSite S T.scheme_mem).Faithful where
  map_injective h := yoneda.map_injective (congrArg (fun q => q.hom) h)

namespace BigFppfSpaceSite

variable {X : T.Spaces} (V : BigFppfSpaceOver T X)

/-- The property of a scheme over the algebraic space underlying `V` that it is affine. -/
def IsAffineSchemeOverSpace :
    ObjectProperty (CostructuredArrow (schemeSpaceFunctor T.schemeSite S T.scheme_mem) V.left) :=
  fun A ↦ IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.left)

/-- **The affine schemes over an object `V` of the big fppf site of `X`**: affine schemes of the
chosen big fppf site of schemes with a morphism from the represented algebraic space to the
algebraic space underlying `V`. -/
abbrev AffineSchemesOver := (IsAffineSchemeOverSpace T V).FullSubcategory

namespace AffineSchemesOver

variable {T V}

/-- The object of the slice `(Spaces/X)_fppf/V` attached to an affine scheme over `V`. -/
abbrev toSliceObj (A : AffineSchemesOver T V) : Over V :=
  Over.mk (Y := Over.mk (A.obj.hom ≫ V.hom)) (Over.homMk A.obj.hom rfl)

variable (T V) in
/-- **The embedding of the affine schemes over `V` into the slice `(Spaces/X)_fppf/V`.** -/
abbrev toSlice : AffineSchemesOver T V ⥤ Over V where
  obj A := toSliceObj A
  map f := Over.homMk (Over.homMk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map f.hom.left)
    (by
      change _ ≫ _ ≫ _ = _ ≫ _
      rw [← Category.assoc, CostructuredArrow.w f.hom]))
    (Over.OverMorphism.ext (CostructuredArrow.w f.hom))
  map_id A := Over.OverMorphism.ext (Over.OverMorphism.ext
    ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_id _))
  map_comp f g := Over.OverMorphism.ext (Over.OverMorphism.ext
    ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_comp _ _))

/-- The algebraic space underlying the image of `A` in the slice is the algebraic space
represented by the scheme underlying `A`. -/
@[simp]
lemma toSlice_obj_left_left (A : AffineSchemesOver T V) :
    ((toSlice T V).obj A).left.left =
      (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A.obj.left := rfl

/-- The morphism of algebraic spaces underlying the image of `f` in the slice is the morphism
represented by the morphism of schemes underlying `f`. -/
@[simp]
lemma toSlice_map_left_left {A A' : AffineSchemesOver T V} (f : A ⟶ A') :
    ((toSlice T V).map f).left.left =
      (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map f.hom.left := rfl

/-- The embedding of the affine schemes over `V` into the slice is faithful. -/
instance toSlice_faithful : (toSlice T V).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_injective
      (congrArg (fun q => q.left.left) h)))

/-- The embedding of the affine schemes over `V` into the slice is full. -/
instance toSlice_full : (toSlice T V).Full where
  map_surjective {A A'} f := by
    obtain ⟨g, hg⟩ := (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_surjective f.left.left
    have h : f.left.left ≫ A'.obj.hom = A.obj.hom := congrArg Over.Hom.left (Over.w f)
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk g (by rw [hg]; exact h)), ?_⟩
    exact Over.OverMorphism.ext (Over.OverMorphism.ext hg)

/-- **The affine schemes over `V` cover every object of the slice at `V`**, for any topology on
the big category of `X` in which every object is covered by its objects represented by affine
schemes. -/
theorem toSlice_isCoverDense_of_generate_mem (V : BigFppfSpaceOver T X)
    (K₀ : GrothendieckTopology (BigFppfSpaceOver T X))
    (hK₀ : ∀ Y : BigFppfSpaceOver T X,
      Sieve.generate (BigFppfSpaceOver.affineSchemePresieve T Y) ∈ K₀ Y) :
    (toSlice T V).IsCoverDense (K₀.over V) where
  is_cover W := by
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ ?_ (hK₀ W.left)
    rw [Sieve.generate_le_iff]
    rintro Z g ⟨Ŵ, hŴ, ⟨e⟩⟩
    rw [Sieve.overEquiv_iff]
    let A : AffineSchemesOver T V :=
      ⟨CostructuredArrow.mk (e.hom ≫ g.left ≫ W.hom.left), hŴ⟩
    refine ⟨⟨A, Over.homMk (Over.homMk e.inv ?_) ?_, Over.homMk (Over.homMk (e.hom ≫ g.left) ?_)
      ?_, ?_⟩⟩
    · refine (e.inv_hom_id_assoc ((g.left ≫ W.hom.left) ≫ V.hom)).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (g.left ≫ ·) (Over.w W.hom)).trans (Over.w g))
    · exact Over.OverMorphism.ext ((e.inv_hom_id_assoc _).trans (Over.comp_left ..).symm)
    · show (e.hom ≫ g.left) ≫ W.left.hom = (e.hom ≫ g.left ≫ W.hom.left) ≫ V.hom
      simp only [Category.assoc, Over.w W.hom]
    · exact Over.OverMorphism.ext ((Over.comp_left ..).trans (Category.assoc _ _ _))
    · exact Over.OverMorphism.ext (Over.OverMorphism.ext (e.inv_hom_id_assoc g.left))

/-- **The affine schemes over `V` cover every object of the slice at `V`.** -/
instance toSlice_isCoverDense :
    (toSlice T V).IsCoverDense ((BigFppfSpaceOver.topology T X).over V) :=
  toSlice_isCoverDense_of_generate_mem V _ (BigFppfSpaceOver.generate_affineSchemePresieve_mem T)

/-- The topology on the affine schemes over `V` induced from the big fppf topology. -/
abbrev topology : GrothendieckTopology (AffineSchemesOver T V) :=
  (toSlice T V).inducedTopology ((BigFppfSpaceOver.topology T X).over V)

/-- An affine scheme together with an identification of the space it represents with the space
underlying `V`, as an affine scheme over `V`. -/
def ofIso (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left) :
    AffineSchemesOver T V :=
  ⟨CostructuredArrow.mk e.hom, hV₀⟩

/-- **An affine scheme identified with `V` is a terminal affine scheme over `V`.** -/
noncomputable def isTerminalOfIso (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left) :
    IsTerminal (ofIso V₀ hV₀ e) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk (CostructuredArrow.homMk
      ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).preimage (A.obj.hom ≫ e.inv))
      ((congrArg (· ≫ e.hom) (Functor.map_preimage _ _)).trans
        ((Category.assoc _ _ _).trans ((congrArg (A.obj.hom ≫ ·) e.inv_hom_id).trans
          (Category.comp_id _))))))
    (fun A f ↦ by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_injective
      have h := CostructuredArrow.w f.hom
      simp only [ofIso, CostructuredArrow.mk_hom_eq_self] at h
      simp only [← h]
      change _ = (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map
        ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).preimage
          (((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map f.hom.left ≫ e.hom) ≫ e.inv))
      exact ((Functor.map_preimage _ _).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e.hom_inv_id).trans (Category.comp_id _)))).symm)

/-- The morphism of affine schemes over `V` given by a morphism of schemes into an affine scheme
over `V`. -/
abbrev homOfScheme (W : AffineSchemesOver T V) {Z : T.Schemes}
    (hZ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z))
    (φ : Z ⟶ W.obj.left) :
    (⟨CostructuredArrow.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map φ ≫ W.obj.hom),
      hZ⟩ : AffineSchemesOver T V) ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk φ rfl)

/-- **A covering sieve of an affine scheme over `V` contains a finite family of affine schemes
over `V` which is an fppf covering family of schemes.** This family also generates a covering
sieve of `W`. -/
theorem exists_finite_fppf_ofArrows_le (W : AffineSchemesOver T V) (R : Sieve W)
    (hR : R ∈ topology W) :
    ∃ (n : ℕ) (Z : Fin n → T.Schemes)
      (hZ : ∀ i, IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i)))
      (φ : ∀ i, Z i ⟶ W.obj.left),
      (∀ i, R (homOfScheme W (hZ i) (φ i))) ∧
        Sieve.ofArrows _ (fun i => homOfScheme W (hZ i) (φ i)) ∈ topology W ∧
        Presieve.ofArrows (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i))
            (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (φ i)) ∈
          Scheme.fppfPrecoverage
            ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W.obj.left) := by
  let F := schemeSpaceFunctor T.schemeSite S T.scheme_mem
  have hsc := fppfSchemeToSpace_isSpecialCocontinuous T
  have := hsc.1
  have := hsc.2
  let R₀ : Sieve (F.obj W.obj.left) :=
    Sieve.overEquiv _ (Sieve.overEquiv _ (R.functorPushforward (toSlice T V)))
  have hR₀ : R₀ ∈ T.topology (F.obj W.obj.left) :=
    (Functor.mem_inducedTopology_iff_of_isCoverDense (G := toSlice T V)
      (K := (BigFppfSpaceOver.topology T X).over V) R).1 hR
  have hpull : R₀.functorPullback F ∈ BigFppfOver.topology T.schemeSite S T.scheme_mem
      W.obj.left := F.cover_lift (J := BigFppfOver.topology T.schemeSite S T.scheme_mem)
        (K := T.topology) hR₀
  obtain ⟨n, Z, φ, haff, hmem, hcov, hfppf⟩ :=
    FibredSite.exists_finite_affine_fppf_ofArrows_le T.schemeSite S T.scheme_mem
      (𝟭 (BigFppfOver T.schemeSite S T.scheme_mem)) Functor.isFiberedInGroupoids_id W.property
      (Sv := R₀.functorPullback F) (by
        rw [BigFppfOver.associatedTopology, Functor.inheritedTopology_id]
        exact hpull)
  rw [BigFppfOver.associatedTopology, Functor.inheritedTopology_id] at hcov
  have himage : ∀ (Q : Sieve W) (i : Fin n), Q (homOfScheme W (haff i) (φ i)) →
      Sieve.overEquiv _ (Sieve.overEquiv _ (Q.functorPushforward (toSlice T V))) (F.map (φ i)) :=
    fun Q i hQ => (Sieve.overEquiv_iff _ _).2 ((Sieve.overEquiv_iff _ _).2
      (Sieve.image_mem_functorPushforward (toSlice T V) Q hQ))
  refine ⟨n, Z, haff, φ, fun i => ?_, ?_, hfppf⟩
  · rw [← (Sieve.fullyFaithfulFunctorGaloisCoinsertion (toSlice T V) W).u_l_eq R]
    exact (Sieve.overEquiv_iff _ _).1 ((Sieve.overEquiv_iff _ _).1 (hmem i))
  · rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
    show Sieve.overEquiv _ (Sieve.overEquiv _
      ((Sieve.ofArrows _ (fun i => homOfScheme W (haff i) (φ i))).functorPushforward
        (toSlice T V))) ∈ T.topology (F.obj W.obj.left)
    refine T.topology.superset_covering ?_ ((Functor.functorPushforward_mem_iff
      (BigFppfOver.topology T.schemeSite S T.scheme_mem) T.topology (G := F)).2 hcov)
    refine (Sieve.functor_galoisConnection F W.obj.left).l_le ?_
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact himage _ i (Sieve.ofArrows_mk _ _ i)

end AffineSchemesOver

end BigFppfSpaceSite

end AlgebraicGeometry

end
