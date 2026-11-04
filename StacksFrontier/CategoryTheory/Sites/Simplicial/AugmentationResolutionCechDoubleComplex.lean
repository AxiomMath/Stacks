module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite

/-!
# The Hom double complex of the resolution of Stacks 0D78, column by column, is the Čech complex

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)`, `G` an
abelian sheaf on `(D, K)` and `W` a complex of abelian sheaves on the total site. The resolution
of Stacks 0D78 gives a double complex `Hom(P_p, W^q)` of abelian groups. This module identifies
its columns and its horizontal differentials with the data of the complex of Stacks 0D79 tested
against `G`:

* the `p`-th column is the Hom complex `Hom(G, a_{p,*}W^•_p)`, by the adjunction
  `g_{p!}∘a_p⁻¹ ⊣ a_{p,*}∘(-)_p` of
  `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermAdjunction` preceded by the
  identification of the degree-`p` term of the resolution with `g_{p!}(a_p⁻¹G)`;
* the horizontal differential is postcomposition with the differential of the complex of
  Stacks 0D79, because the mate of a cosimplicial transition of that complex is the corresponding
  structure map of the resolution, which is
  `CategoryTheory.SimplicialSiteSituation.Augmentation.conjugateEquiv_cechDifferential_app'`, read
  through `CategoryTheory.Adjunction.homEquiv_conjugateEquiv`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechCoyonedaColumn`: the Hom complex
  `Hom(G, a_{p,*}W^•_p)` out of `G` into the degree-`p` term of the complex of Stacks 0D79.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechCoyonedaDoubleComplex`: the double
  complex `Hom(G, a_{p,*}W^q_p)` those columns and that horizontal differential assemble into.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechDifferential_comp`: the differentials
  of the complex of Stacks 0D79 compose to zero, as natural transformations.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.homEquiv_degIso_inv_comp_d`: **the
  horizontal compatibility**, as the transposition identity it reduces to.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechColumnIso`: **the column
  identification.**
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechDoubleComplexIso`: **the two double
  complexes are isomorphic**, the column identification and the horizontal compatibility
  assembled.

## Implementation notes

`degIso'` is used rather than `Resolution.degreeIso` for the anchoring reason recorded in
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationCechTermMate.lean`: the comparison
lemmas are stated at `(barSimplicial' …).obj (op ⦋k⦌)`, and a composite anchored at the other
spelling does not admit their rewrites.

`cechDoubleComplexIso` compares the two horizontal differentials on elements, through the
`_d_f_apply` lemmas of the two double complexes and `cechColumnIso_hom_f_apply`. Two rewrites that
one would expect to work do not, and both are replaced by terms.

`CategoryTheory.comp_apply` does not fire on the goal `ext` leaves: it is stated at
`ConcreteCategory.hom` while the goal carries `AddCommGrpCat.Hom.hom`, and the two are only
definitionally equal. A `show` splitting the composite is used instead, and it is kept to the
composite alone — stating the whole equation with `change` is what exhausts the heartbeat budget,
because the `homEquiv` inside `cechColumnIso` is then unfolded at default transparency.

For the same reason the horizontal differential is named, as `cechCoyonedaDoubleComplexD`, rather
than written inline into `CochainComplex.of`. Computing it on an element is a `rfl` through
`preadditiveCoyoneda` and its `ModuleCat` detour, and that `rfl` fits in the heartbeat budget only
when it is asked about the named morphism: asked about `(CochainComplex.of …).d p (p + 1)`, with or
without the `Eq.mpr` a rewrite of the `of`-equation leaves behind, `whnf` exhausts the budget. So
`cechCoyonedaDoubleComplexD_f_apply` is the `rfl`, and the statement about the complex's own
differential is that lemma transported along the `of`-equation by `congrArg`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u})

section

variable [HasSheafify K Ab.{u}]

omit [HasSheafify K Ab.{u}] in
/-- **The differentials of the complex of Stacks 0D79 compose to zero**, as natural
transformations between its terms. -/
theorem cechDifferential_comp (p : ℕ) :
    cechDifferential S D K a p ≫ cechDifferential S D K a (p + 1) = 0 := by
  apply NatTrans.ext
  funext F
  have h := (augmentedCechComplex S D K a F).d_comp_d (p + 1) (p + 2) (p + 3)
  rw [augmentedCechComplex_d_eq, augmentedCechComplex_d_eq] at h
  change (cechDifferential S D K a p).app F ≫ (cechDifferential S D K a (p + 1)).app F = 0
  exact h

/-- **The transposition identity behind the horizontal compatibility of the two double
complexes**: transposing along `cechTermAdjunction` in degree `p + 1` a morphism precomposed with
the differential of the resolution of Stacks 0D78 is transposing it in degree `p` and
postcomposing with the differential of the complex of Stacks 0D79. -/
theorem homEquiv_degIso_inv_comp_d (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    (p : ℕ) (q : ℤ) (f : (resolutionComplex S D K a G).X p ⟶ W.X q) :
    (cechTermAdjunction S D K a ⦋p⦌).homEquiv G (W.X q)
          ((degIso' S D K a G p).inv ≫ f) ≫
        (cechDifferential S D K a p).app (W.X q) =
      (cechTermAdjunction S D K a ⦋p + 1⦌).homEquiv G (W.X q)
        ((degIso' S D K a G (p + 1)).inv ≫
          (resolutionComplex S D K a G).d (p + 1) p ≫ f) := by
  have harg : ((conjugateEquiv (cechTermAdjunction S D K a ⦋p⦌)
        (cechTermAdjunction S D K a ⦋p + 1⦌)).symm
          (cechDifferential S D K a p)).app G ≫ ((degIso' S D K a G p).inv ≫ f) =
      (degIso' S D K a G (p + 1)).inv ≫ (resolutionComplex S D K a G).d (p + 1) p ≫ f := by
    have hc := Iso.hom_inv_id_assoc (degIso' S D K a G p) f
    rw [conjugateEquiv_cechDifferential_app' S D K a G p, Category.assoc, Category.assoc, hc]
    rfl
  rw [← Equiv.apply_symm_apply (conjugateEquiv (cechTermAdjunction S D K a ⦋p⦌)
    (cechTermAdjunction S D K a ⦋p + 1⦌)) (cechDifferential S D K a p),
    ← Adjunction.homEquiv_conjugateEquiv (cechTermAdjunction S D K a ⦋p⦌)
    (cechTermAdjunction S D K a ⦋p + 1⦌), harg]

/-- The `p`-th column of the double complex `Hom(G, a_{p,*}W^q_p)`: the Hom complex out of `G`
into the degree-`p` term of the complex of Stacks 0D79, applied degreewise to `W`. -/
abbrev cechCoyonedaColumn (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.coyonedaComplex G
    (((abelianComponentPushforward S D K a ⦋p⦌).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W)

/-- **The `p`-th column of the Hom double complex of the resolution of Stacks 0D78 is the Hom
complex out of `G` into the degree-`p` term of the complex of Stacks 0D79.** -/
def cechColumnIso (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) :
    (CochainComplex.homProductDoubleComplex (resolutionComplex S D K a G) W).X p ≅
      cechCoyonedaColumn S D K a G W p := by
  letI := additive_cechTermLowerShriek S D K a ⦋p⦌
  letI := additive_componentAugmentationPushforwardAb S D K a ⦋p⦌
  refine ?_ ≪≫ CochainComplex.coyonedaComplexAdjIso (cechTermAdjunction S D K a ⦋p⦌) G W
  exact ((NatIso.mapHomologicalComplex
    (preadditiveCoyoneda.mapIso (degIso' S D K a G p).op)
    (ComplexShape.up ℤ)).app W).symm

/-- The column identification on an element: it is the transposition along `cechTermAdjunction`
of the morphism precomposed with the degree-`p` identification of the resolution's term. -/
theorem cechColumnIso_hom_f_apply (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    (p : ℕ) (q : ℤ) (f : (resolutionComplex S D K a G).X p ⟶ W.X q) :
    (cechColumnIso S D K a G W p).hom.f q f =
      (cechTermAdjunction S D K a ⦋p⦌).homEquiv G (W.X q)
        ((degIso' S D K a G p).inv ≫ f) :=
  rfl

/-- **The double complex `Hom(G, a_{p,*}W^q_p)` of the complex of Stacks 0D79 tested against
`G`.** Its `p`-th column is the Hom complex out of `G` into the degree-`p` term of the complex of
Stacks 0D79 applied degreewise to `W`, and its horizontal differential is postcomposition with
the differential of that complex. -/
def cechCoyonedaDoubleComplexD (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) :
    cechCoyonedaColumn S D K a G W p ⟶ cechCoyonedaColumn S D K a G W (p + 1) :=
  ((preadditiveCoyoneda.obj (Opposite.op G)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex (cechDifferential S D K a p) (ComplexShape.up ℤ)).app W)

/-- The horizontal differential of the double complex of Stacks 0D79 tested against `G`, on an
element: postcomposition with the differential of that complex. -/
theorem cechCoyonedaDoubleComplexD_f_apply
    (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) (q : ℤ)
    (f : G ⟶ (abelianComponentPushforward S D K a ⦋p⦌).obj (W.X q)) :
    (cechCoyonedaDoubleComplexD S D K a G W p).f q f =
      f ≫ (cechDifferential S D K a p).app (W.X q) :=
  rfl

/-- The horizontal differentials of the double complex of Stacks 0D79 tested against `G` compose
to zero. -/
theorem cechCoyonedaDoubleComplexD_comp
    (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) :
    cechCoyonedaDoubleComplexD S D K a G W p ≫
        cechCoyonedaDoubleComplexD S D K a G W (p + 1) = 0 := by
  ext q (f : G ⟶ (abelianComponentPushforward S D K a ⦋p⦌).obj (W.X q))
  change f ≫ (cechDifferential S D K a p).app (W.X q) ≫
    (cechDifferential S D K a (p + 1)).app (W.X q) = 0
  rw [← NatTrans.comp_app, cechDifferential_comp, NatTrans.app_zero]
  exact Limits.comp_zero

/-- **The double complex `Hom(G, a_{p,*}W^q_p)` of the complex of Stacks 0D79 tested against
`G`.** Its `p`-th column is the Hom complex out of `G` into the degree-`p` term of the complex of
Stacks 0D79 applied degreewise to `W`, and its horizontal differential is postcomposition with
the differential of that complex. -/
def cechCoyonedaDoubleComplex (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  CochainComplex.of (cechCoyonedaColumn S D K a G W)
    (cechCoyonedaDoubleComplexD S D K a G W) (cechCoyonedaDoubleComplexD_comp S D K a G W)

/-- The horizontal differential of the double complex of Stacks 0D79 tested against `G` is
postcomposition with the differential of that complex. -/
theorem cechCoyonedaDoubleComplex_d (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    (p : ℕ) :
    (cechCoyonedaDoubleComplex S D K a G W).d p (p + 1) =
      cechCoyonedaDoubleComplexD S D K a G W p := by
  dsimp only [cechCoyonedaDoubleComplex]
  exact CochainComplex.of_d _ _ _

/-- The horizontal differential of the double complex of Stacks 0D79 tested against `G`, read off
the complex, on an element. -/
theorem cechCoyonedaDoubleComplex_d_f_apply
    (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (p : ℕ) (q : ℤ)
    (f : G ⟶ (abelianComponentPushforward S D K a ⦋p⦌).obj (W.X q)) :
    ((cechCoyonedaDoubleComplex S D K a G W).d p (p + 1)).f q f =
      f ≫ (cechDifferential S D K a p).app (W.X q) := by
  rw [cechCoyonedaDoubleComplex_d]
  exact cechCoyonedaDoubleComplexD_f_apply S D K a G W p q f

/-- **The Hom double complex of the resolution of Stacks 0D78 is the double complex of the
complex of Stacks 0D79 tested against `G`.** Column by column this is `cechColumnIso`; the
horizontal differentials agree by `homEquiv_degIso_inv_comp_d`, the transposition identity which
says that precomposing with the differential of the resolution is postcomposing with the
differential of the complex of Stacks 0D79. -/
def cechDoubleComplexIso (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    CochainComplex.homProductDoubleComplex (resolutionComplex S D K a G) W ≅
      cechCoyonedaDoubleComplex S D K a G W :=
  HomologicalComplex.Hom.isoOfComponents (cechColumnIso S D K a G W)
    fun p p' hpp' => by
      obtain rfl : p + 1 = p' := hpp'
      apply HomologicalComplex.hom_ext
      intro q
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      ext (f : (resolutionComplex S D K a G).X p ⟶ W.X q)
      change ((cechCoyonedaDoubleComplex S D K a G W).d p (p + 1)).f q
            ((cechColumnIso S D K a G W p).hom.f q f) =
          (cechColumnIso S D K a G W (p + 1)).hom.f q
            (((CochainComplex.homProductDoubleComplex (resolutionComplex S D K a G) W).d p
              (p + 1)).f q f)
      refine Eq.trans (cechCoyonedaDoubleComplex_d_f_apply S D K a G W p q
        ((cechColumnIso S D K a G W p).hom.f q f)) ?_
      refine Eq.trans (congrArg (fun t => t ≫ (cechDifferential S D K a p).app (W.X q))
        (cechColumnIso_hom_f_apply S D K a G W p q f)) ?_
      refine Eq.trans (homEquiv_degIso_inv_comp_d S D K a G W p q f) ?_
      refine Eq.trans (congrArg (fun t =>
          (cechTermAdjunction S D K a ⦋p + 1⦌).homEquiv G (W.X q)
            ((degIso' S D K a G (p + 1)).inv ≫ t))
        (CochainComplex.homProductDoubleComplex_d_f_apply
          (resolutionComplex S D K a G) W p q f).symm) ?_
      exact (cechColumnIso_hom_f_apply S D K a G W (p + 1) q
        (((CochainComplex.homProductDoubleComplex (resolutionComplex S D K a G) W).d p
          (p + 1)).f q f)).symm

end

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
