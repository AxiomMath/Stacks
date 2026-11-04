module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceStalkInjectivity
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceTransitivity
public import StacksFrontier.AlgebraicTopology.SimplexCoproductAcyclicity

/-!
# The Čech complex of an open covering for the direct image with compact support

Let `f : X ⟶ Y` be a locally quasi-finite morphism in a big étale site and let `X = ⋃_{i ∈ I} X_i`
be a covering of `X` by open subschemes. Writing `X_{i₀…i_p} = X_{i₀} ∩ … ∩ X_{i_p}` and
`f_{i₀…i_p}` for the restriction of `f`, there is a chain complex

`… → ⊕_{i₀,i₁,i₂} f_{i₀i₁i₂,!} F|_{X_{i₀i₁i₂}} → ⊕_{i₀,i₁} f_{i₀i₁,!} F|_{X_{i₀i₁}} →
  ⊕_{i₀} f_{i₀,!} F|_{X_{i₀}} → f_! F → 0`

of abelian étale sheaves on `Y`, with the Čech sign rule, functorial in `F`. This is the complex
of Stacks 0F5H; it is built here as the augmented alternating-face-map complex of a Čech
simplicial object in the category of functors `Ab(X_étale) ⥤ Ab(Y_étale)`, so that functoriality
in `F` is part of the construction rather than an extra statement.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.shriekLE` — the covariance map
  `(j_V ≫ f)_!(F|_V) ⟶ (j_W ≫ f)_!(F|_W)` attached to an inclusion `V ≤ W` of opens of `X`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechSimplicial` — the Čech simplicial object whose
  `p`-th term is `⊕_{i₀…i_p} f_{i₀…i_p,!}(-)|_{X_{i₀…i_p}}`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplex` — **Stacks 0F5H**, the complex itself.

## Main results

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.shriekLE_trans` — the covariance maps of an
  inclusion of opens compose, so that the Čech faces satisfy the simplicial identities.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplex_d_one_zero` — the last differential is
  the sum of the covariance maps `f_{i₀,!}((-)|_{X_{i₀}}) ⟶ f_!(-)`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.alternatingFaceMapComplex_cechSimplicial_d` — above
  degree one the differential is the alternating sum of the face maps deleting one index.

## Implementation notes

The only coherence needed for the faces is that the covariance map of an inclusion of opens
composes, `shriekLE_trans`. It is *not* proved from a pentagon identity for the comparison
isomorphism `openShriekCompIso` -- no such identity is available -- but by cancelling the
covariance map `f_{W,!}(F|_W) ⟶ f_! F`, which is a monomorphism by Stacks 0F6S part (4). Both
sides of `shriekLE_trans` become the covariance map of the smallest open after that cancellation,
by Stacks 0F6S part (3). The same cancellation gives `shriekLE_refl`, so a genuine simplicial
object is obtained and Mathlib's alternating-face-map complex supplies `d ∘ d = 0`.

Since the morphisms of the site between two open subschemes of `X` over `X` are unique, the
inclusions may be taken to be the maps `Scheme.homOfLE` of the poset of opens; transporting the
direct image with compact support along the equality `homOfLE h ≫ j_W = j_V` of morphisms of the
site is the only `eqToHom` in the construction.

## References

* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

open scoped Simplicial

universe u v

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

/-- The category in which the Čech complex of an open covering lives: functors from abelian
sheaves on the small étale site of `X` to abelian sheaves on the small étale site of `Y`. -/
public abbrev ShriekCat (B : BigEtaleSite.{u}) (X Y : B.Scheme) :=
  Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

section OpenSubscheme

/-- An open subscheme of an object of a big étale site, as an object of that site: an open
subscheme is no larger than the scheme it sits in. -/
public def openScheme (V : (B.inclusion.obj X).Opens) : B.Scheme :=
  ⟨V.toScheme, (Scheme.size_coe_opens_le (B.inclusion.obj X) V).trans_lt X.property⟩

/-- The inclusion of an open subscheme, as a morphism of the big étale site. -/
public def openSchemeι (V : (B.inclusion.obj X).Opens) : openScheme B V ⟶ X :=
  ObjectProperty.homMk V.ι

/-- The inclusion of an open subscheme is an open immersion. -/
public instance (V : (B.inclusion.obj X).Opens) :
    IsOpenImmersion (B.inclusion.map (openSchemeι B V)) :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- The inclusion of one open subscheme of `X` into a larger one, as a morphism of the site. -/
public def openSchemeLE {V W : (B.inclusion.obj X).Opens} (h : V ≤ W) :
    openScheme B V ⟶ openScheme B W :=
  ObjectProperty.homMk ((B.inclusion.obj X).homOfLE h)

/-- The inclusion of one open subscheme into a larger one is an open immersion. -/
public instance {V W : (B.inclusion.obj X).Opens} (h : V ≤ W) :
    IsOpenImmersion (B.inclusion.map (openSchemeLE B h)) :=
  inferInstanceAs (IsOpenImmersion ((B.inclusion.obj X).homOfLE h))

/-- The inclusion of a smaller open subscheme factors the inclusion of a larger one. -/
public theorem openSchemeLE_ι {V W : (B.inclusion.obj X).Opens} (h : V ≤ W) :
    openSchemeLE B h ≫ openSchemeι B W = openSchemeι B V :=
  ObjectProperty.hom_ext _ ((B.inclusion.obj X).homOfLE_ι h)

end OpenSubscheme

section FaceMap

/-- Equal open immersions of the source have equal direct images with compact support of the
restricted sheaf. -/
public theorem openShriekPushforward_congr {X' : B.Scheme} (g g' : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map g)] [IsOpenImmersion (B.inclusion.map g')]
    (hg : g = g') :
    openShriekPushforward.{u, v} B g f = openShriekPushforward.{u, v} B g' f := by
  cases hg
  rfl

/-- The covariance maps of two equal open immersions of the source agree, after the transport
identifying their direct images with compact support. -/
public theorem eqToHom_comp_openCovarianceShriekMap {X' : B.Scheme} (g g' : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map g)] [IsOpenImmersion (B.inclusion.map g')]
    (hg : g = g') :
    eqToHom (openShriekPushforward_congr.{u, v} B f g g' hg) ≫
        openCovarianceShriekMap.{u, v} B g' f =
      openCovarianceShriekMap.{u, v} B g f := by
  cases hg
  simp

/-- **The Čech face map.** For an inclusion `V ≤ W` of open subschemes of `X`, the covariance map
`(j_V ≫ f)_!((-)|_V) ⟶ (j_W ≫ f)_!((-)|_W)` of Stacks 0F6S for the open immersion `V ⟶ W`. -/
@[stacks 0F6S "covariance along an inclusion of opens of the source"]
public def shriekLE {V W : (B.inclusion.obj X).Opens} (h : V ≤ W) :
    openShriekPushforward.{u, v} B (openSchemeι B V) f ⟶
      openShriekPushforward.{u, v} B (openSchemeι B W) f :=
  eqToHom (openShriekPushforward_congr.{u, v} B f (openSchemeι B V)
      (openSchemeLE B h ≫ openSchemeι B W) (openSchemeLE_ι B h).symm) ≫
    (openShriekCompIso.{u, v} B (openSchemeLE B h) (openSchemeι B W) f).hom ≫
    Functor.whiskerLeft (openRestriction.{u, v} B (openSchemeι B W))
      (openCovarianceShriekMap.{u, v} B (openSchemeLE B h) (openSchemeι B W ≫ f))

/-- The Čech face map of an inclusion of opens, followed by the covariance map of the larger
open, is the covariance map of the smaller open. -/
public theorem shriekLE_comp_openCovarianceShriekMap {V W : (B.inclusion.obj X).Opens}
    (h : V ≤ W) :
    shriekLE.{u, v} B f h ≫ openCovarianceShriekMap.{u, v} B (openSchemeι B W) f =
      openCovarianceShriekMap.{u, v} B (openSchemeι B V) f := by
  rw [shriekLE]
  simp only [Category.assoc]
  rw [openCovarianceShriekMap_comp.{u, v} B (openSchemeLE B h) (openSchemeι B W) f]
  exact eqToHom_comp_openCovarianceShriekMap.{u, v} B f _ _ (openSchemeLE_ι B h).symm

/-- **Stacks 0F6S, part (4).** The covariance map of an open immersion of the source is a
monomorphism of functors, since it is one on every abelian sheaf. -/
public instance mono_openCovarianceShriekMap_functor {X' : B.Scheme} (g : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map g)] :
    Mono (openCovarianceShriekMap.{u, v} B g f) := by
  have : ∀ F, Mono ((openCovarianceShriekMap.{u, v} B g f).app F) := fun F =>
    mono_openCovarianceShriekMap_app_general.{u, v} B g f F
  exact NatTrans.mono_of_mono_app _

/-- The Čech face maps compose: for `V ≤ W ≤ Z` the face map of `V ≤ Z` is the composite of the
face maps of `V ≤ W` and of `W ≤ Z`. -/
public theorem shriekLE_trans {V W Z : (B.inclusion.obj X).Opens} (h₁ : V ≤ W) (h₂ : W ≤ Z) :
    shriekLE.{u, v} B f h₁ ≫ shriekLE.{u, v} B f h₂ = shriekLE.{u, v} B f (h₁.trans h₂) := by
  refine (cancel_mono (openCovarianceShriekMap.{u, v} B (openSchemeι B Z) f)).1 ?_
  rw [Category.assoc, shriekLE_comp_openCovarianceShriekMap,
    shriekLE_comp_openCovarianceShriekMap, shriekLE_comp_openCovarianceShriekMap]

/-- The Čech face map of an open subscheme in itself is the identity. -/
public theorem shriekLE_refl {V : (B.inclusion.obj X).Opens} (h : V ≤ V) :
    shriekLE.{u, v} B f h = 𝟙 _ := by
  refine (cancel_mono (openCovarianceShriekMap.{u, v} B (openSchemeι B V) f)).1 ?_
  rw [shriekLE_comp_openCovarianceShriekMap, Category.id_comp]

end FaceMap

section Complex

/-- The category `ShriekCat B X Y` has coproducts indexed by any type of the universe of its
sheaves: they are computed objectwise in abelian sheaves on the small étale site of `Y`. -/
public instance hasColimitsOfShape_shriekCat (J : Type (max (u + 1) v)) :
    HasColimitsOfShape (Discrete J) (ShriekCat.{u, v} B X Y) := by
  have h : HasColimitsOfShape (Discrete J)
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  exact Limits.functorCategoryHasColimitsOfShape

/-- Every family of objects of `ShriekCat B X Y` indexed by a type of the universe of its sheaves
has a coproduct. -/
public instance hasCoproduct_shriekCat {J : Type (max (u + 1) v)}
    (A : J → ShriekCat.{u, v} B X Y) : HasCoproduct A :=
  (hasColimitsOfShape_shriekCat.{u, v} B J).has_colimit _

variable {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- The open subscheme `X_{i₀…i_p} = X_{i₀} ∩ … ∩ X_{i_p}` cut out by a tuple of indices. -/
public def coverOpen {n : ℕ} (t : Fin n → I) : (B.inclusion.obj X).Opens := ⨅ k, U (t k)

/-- Deleting entries from a tuple of indices enlarges the intersection of the corresponding
opens. -/
public theorem coverOpen_le_comp {m n : ℕ} (t : Fin m → I) (g : Fin n → Fin m) :
    coverOpen B U t ≤ coverOpen B U (t ∘ g) :=
  le_iInf fun l => iInf_le _ (g l)

/-- The family of summands `f_{i₀…i_p,!}((-)|_{X_{i₀…i_p}})` of the degree-`p` term of the Čech
complex, indexed by the tuples of indices of length `n = p + 1`. -/
public abbrev cechFamily (n : ℕ) : (Fin n → I) → ShriekCat.{u, v} B X Y := fun t =>
  openShriekPushforward.{u, v} B (openSchemeι B (coverOpen B U t)) f

/-- The map of Čech terms induced by a reindexing of tuples: on the summand of a tuple `t` it is
the face map of the inclusion `X_t ⊆ X_{t ∘ g}` into the summand of `t ∘ g`. -/
public def cechMap {m n : ℕ} (g : Fin n → Fin m) :
    (∐ cechFamily.{u, v} B f U m) ⟶ ∐ cechFamily.{u, v} B f U n :=
  Sigma.desc fun t => shriekLE.{u, v} B f (coverOpen_le_comp B U t g) ≫
    Sigma.ι (cechFamily.{u, v} B f U n) (t ∘ g)

/-- The reindexing map of Čech terms on the summand of a tuple. -/
public theorem ι_comp_cechMap {m n : ℕ} (g : Fin n → Fin m) (t : Fin m → I) :
    Sigma.ι (cechFamily.{u, v} B f U m) t ≫ cechMap.{u, v} B f U g =
      shriekLE.{u, v} B f (coverOpen_le_comp B U t g) ≫
        Sigma.ι (cechFamily.{u, v} B f U n) (t ∘ g) :=
  colimit.ι_desc _ _

/-- The identity reindexing acts as the identity on Čech terms. -/
public theorem cechMap_id {m : ℕ} : cechMap.{u, v} B f U (id : Fin m → Fin m) = 𝟙 _ :=
  Sigma.hom_ext _ _ fun t =>
    (ι_comp_cechMap.{u, v} B f U _ t).trans
      ((congrArg (· ≫ Sigma.ι (cechFamily.{u, v} B f U m) t)
          (shriekLE_refl.{u, v} B f _)).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- Reindexing of Čech terms is contravariantly functorial. -/
public theorem cechMap_comp {m n p : ℕ} (g : Fin n → Fin m) (g' : Fin p → Fin n) :
    cechMap.{u, v} B f U (g ∘ g') = cechMap.{u, v} B f U g ≫ cechMap.{u, v} B f U g' := by
  refine Sigma.hom_ext _ _ fun t => ?_
  rw [ι_comp_cechMap, ← Category.assoc, ι_comp_cechMap, Category.assoc, ι_comp_cechMap,
    ← Category.assoc, shriekLE_trans]
  rfl

/-- **The Čech simplicial object of an open covering.** Its term in degree `p` is the direct sum
`⊕_{i₀…i_p} f_{i₀…i_p,!}((-)|_{X_{i₀…i_p}})` over the tuples of `p + 1` indices, and a map of
simplices acts by the covariance maps of the corresponding inclusions of opens. -/
public def cechSimplicial : SimplicialObject (ShriekCat.{u, v} B X Y) where
  obj n := ∐ cechFamily.{u, v} B f U (n.unop.len + 1)
  map φ := cechMap.{u, v} B f U φ.unop.toOrderHom
  map_id _ := cechMap_id.{u, v} B f U
  map_comp φ ψ := cechMap_comp.{u, v} B f U φ.unop.toOrderHom ψ.unop.toOrderHom

/-- The `i`-th face of the Čech simplicial object deletes the `i`-th index of a tuple. -/
public theorem cechSimplicial_δ {n : ℕ} (i : Fin (n + 2)) :
    (cechSimplicial.{u, v} B f U).δ i = cechMap.{u, v} B f U i.succAbove :=
  rfl

/-- The augmentation of the Čech complex: the sum of the covariance maps
`f_{i₀…i_p,!}((-)|_{X_{i₀…i_p}}) ⟶ f_!(-)` of Stacks 0F6S over the tuples of indices. -/
public def cechAugMap (n : ℕ) : (∐ cechFamily.{u, v} B f U n) ⟶ fShriekFunctor.{u, v} B f :=
  Sigma.desc fun t => openCovarianceShriekMap.{u, v} B (openSchemeι B (coverOpen B U t)) f

/-- The augmentation on the summand of a tuple is the covariance map of that intersection. -/
public theorem ι_comp_cechAugMap {n : ℕ} (t : Fin n → I) :
    Sigma.ι (cechFamily.{u, v} B f U n) t ≫ cechAugMap.{u, v} B f U n =
      openCovarianceShriekMap.{u, v} B (openSchemeι B (coverOpen B U t)) f :=
  colimit.ι_desc _ _

/-- The augmentation is compatible with every reindexing of tuples, so it is a map from the Čech
simplicial object to a constant one. -/
public theorem cechMap_comp_cechAugMap {m n : ℕ} (g : Fin n → Fin m) :
    cechMap.{u, v} B f U g ≫ cechAugMap.{u, v} B f U n = cechAugMap.{u, v} B f U m := by
  refine Sigma.hom_ext _ _ fun t => ?_
  rw [← Category.assoc, ι_comp_cechMap, Category.assoc, ι_comp_cechAugMap, ι_comp_cechAugMap,
    shriekLE_comp_openCovarianceShriekMap]

/-- **The augmented Čech simplicial object.** The augmentation `⊕_{i₀} f_{i₀,!}((-)|_{X_{i₀}})
⟶ f_!` is the sum of the covariance maps of Stacks 0F6S. -/
public def cechAugmented : SimplicialObject.Augmented (ShriekCat.{u, v} B X Y) where
  left := cechSimplicial.{u, v} B f U
  right := fShriekFunctor.{u, v} B f
  hom :=
    { app n := cechAugMap.{u, v} B f U (n.unop.len + 1)
      naturality _ _ φ :=
        (cechMap_comp_cechAugMap.{u, v} B f U φ.unop.toOrderHom).trans
          (Category.comp_id _).symm }

/-- **Stacks 0F5H.** The Čech complex of an open covering `X = ⋃_{i ∈ I} X_i` for the direct
image with compact support along a locally quasi-finite morphism `f : X ⟶ Y`: a complex

`… → ⊕_{i₀,i₁} f_{i₀i₁,!}((-)|_{X_{i₀i₁}}) → ⊕_{i₀} f_{i₀,!}((-)|_{X_{i₀}}) → f_!(-) → 0`

of functors on abelian sheaves on the small étale site of `X`, hence functorial in the sheaf. -/
@[stacks 0F5H "the complex, functorial in the abelian sheaf"]
public def cechComplex : ChainComplex (ShriekCat.{u, v} B X Y) ℕ :=
  (AlternatingFaceMapComplex.obj (cechAugmented.{u, v} B f U).left).augment
    ((cechAugmented.{u, v} B f U).hom.app (op ⦋0⦌))
    (SimplexCoproductAcyclicity.d_one_zero_comp_hom_app (cechAugmented.{u, v} B f U))

/-- The complex ends in `f_!` in degree zero. -/
public theorem cechComplex_X_zero :
    (cechComplex.{u, v} B f U).X 0 = fShriekFunctor.{u, v} B f :=
  rfl

/-- In degree `p + 1` the complex is the direct sum over the tuples of `p + 1` indices. -/
public theorem cechComplex_X_succ (n : ℕ) :
    (cechComplex.{u, v} B f U).X (n + 1) = ∐ cechFamily.{u, v} B f U (n + 1) :=
  rfl

/-- The last differential of the complex is the sum of the covariance maps
`f_{i₀,!}((-)|_{X_{i₀}}) ⟶ f_!(-)`, so the complex ends `… → ⊕_{i₀} f_{i₀,!} F|_{X_{i₀}} →
f_! F → 0`. -/
public theorem cechComplex_d_one_zero :
    (cechComplex.{u, v} B f U).d 1 0 = cechAugMap.{u, v} B f U 1 :=
  rfl

/-- Above degree one the differential of the complex is the differential of the alternating-face
map complex of the Čech simplicial object. -/
public theorem cechComplex_d_succ_succ (n : ℕ) :
    (cechComplex.{u, v} B f U).d (n + 2) (n + 1) =
      (AlternatingFaceMapComplex.obj (cechSimplicial.{u, v} B f U)).d (n + 1) n :=
  ChainComplex.augment_d_succ_succ _ _ _ (n + 1) n

/-- The differential of the alternating-face map complex of the Čech simplicial object is the
alternating sum of the face maps deleting one index from a tuple: the Čech sign rule. -/
public theorem alternatingFaceMapComplex_cechSimplicial_d (n : ℕ) :
    (AlternatingFaceMapComplex.obj (cechSimplicial.{u, v} B f U)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cechMap.{u, v} B f U i.succAbove :=
  AlternatingFaceMapComplex.obj_d_eq _ n

/-- **Stacks 0F5H**, at a fixed abelian sheaf: the Čech complex of the covering for `F`, a complex
of abelian sheaves on the small étale site of `Y` whose degree-zero term is `f_! F`. It is the
value at `F` of the complex of functors, so it is functorial in `F`. -/
public def cechComplexObj
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    ChainComplex
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) ℕ :=
  (((evaluation _ _).obj F).mapHomologicalComplex _).obj (cechComplex.{u, v} B f U)

/-- The complex of `F` ends in `f_! F` in degree zero. -/
public theorem cechComplexObj_X_zero
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (cechComplexObj.{u, v} B f U F).X 0 = (fShriekFunctor.{u, v} B f).obj F :=
  rfl

/-- In degree `p + 1` the complex of `F` is the direct sum of the `f_{i₀…i_p,!} F|_{X_{i₀…i_p}}`
over the tuples of `p + 1` indices. -/
public theorem cechComplexObj_X_succ (n : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (cechComplexObj.{u, v} B f U F).X (n + 1) = (∐ cechFamily.{u, v} B f U (n + 1)).obj F :=
  rfl

end Complex

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
