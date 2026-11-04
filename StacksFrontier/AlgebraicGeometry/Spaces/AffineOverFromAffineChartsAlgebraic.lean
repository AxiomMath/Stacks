module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound

/-!
# A sheaf over an algebraic space which is affine over its affine charts

Let `X` be an algebraic space over `S` and `π : F ⟶ X` a morphism from an fppf sheaf `F` whose
base change to every affine étale chart `V` of `X` is represented by an affine scheme `W_V`.  This
file shows that `F` is an algebraic space and `π` is affine, provided the sizes of the `W_V` are
bounded by one cardinal below the cutoff of the site.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas`: the statement
  over the affine opens of one surjective étale atlas `U ⟶ X`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_affineChart` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_and_isAffineHom_of_affineChart`: the
  statement over all affine étale charts of `X`.

## Implementation notes

**The proof.**  Over an affine open `V` of the atlas `U` the base change `F ×_X V` is the affine
scheme `W_V`, so `F ×_X U` is glued from the `W_V` along the affine opens of `U`
(`AlgebraicGeometry.Space.exists_representing_over_of_openCover_of_size_le`) and is a scheme
affine over `U`.  Affine morphisms descend effectively along surjective étale morphisms
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`), so Stacks 03I2
(`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`)
makes `F` an algebraic space and `π` representable and affine.

**Why the uniform size bound `μ` is needed.**  Without it the statement is false in this
size-bounded site.  The cutoff `κ` of a big fppf site is a strong limit of uncountable
cofinality, but need not be regular: take `κ = ℶ_{ω₁}`.  Let `X` be the disjoint union of `ω₁`
copies of `Spec 𝔽_p` (an object of the site) and `K_α`, `α < ω₁`, fields with `#K_α` cofinal in
`κ`; let `F` be the functor of points of the scheme `∐_α Spec K_α` over `X`, restricted to the
site.  An affine étale chart of `X` is quasi-compact, so meets finitely many components, and the
base change of `F` to it is an affine object of the site.  But `F` has no atlas in the site: a
surjective étale scheme over `Spec K_α` has residue fields of cardinality at least `#K_α`, so an
atlas of `F` would have size at least `κ`.  The gluing of the `W_V` over the affine opens of an
atlas needs exactly a bound on their sizes uniform below the cutoff, because the number of those
opens may reach the cofinality of `κ`.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf over an algebraic space which is a bounded affine scheme over the affine opens of an
atlas is an algebraic space, affine over the base.**  Let `a : U ⟶ Y` be a surjective étale atlas
of an algebraic space `Y` and `π : F ⟶ Y` a morphism from an fppf sheaf.  If over every affine open
`V` of `U` the base change of `π` along `V ⟶ U ⟶ Y` is represented by an affine scheme of size at
most `μ`, for one cardinal `μ` below the cutoff, then `F` is an algebraic space and `π` is
representable with affine represented base changes. -/
theorem isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas
    {Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ Y)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (h : ∀ (V : BigFppfOver B S hS) (u : V ⟶ U),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F) (q : W ⟶ V),
        IsPullback p (yoneda.map q) π (yoneda.map u ≫ a) ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ) :
    IsAlgebraicSpace B S hS F ∧
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf π := by
  have hRI : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- the affine opens of the atlas, as objects of the site
  choose V u hu hurange hVaff using
    fun O => BigFppfOver.exists_affineOpen_restrict B S hS U O
  choose W p q hpb hWaff hWsize using fun O => h (V O) (u O) (hu O) (hVaff O)
  have hpbU : IsPullback (pullback.fst π a) (pullback.snd π a) π a := IsPullback.of_hasPullback π a
  -- over each affine open, the base change of `F ×_Y U ⟶ U` is the affine scheme `W`
  have hpb' : ∀ O, IsPullback (hpbU.lift (p O) (yoneda.map (q O) ≫ yoneda.map (u O))
      (by rw [(hpb O).w, Category.assoc])) (yoneda.map (q O)) (pullback.snd π a)
      (yoneda.map (u O)) := fun O => IsPullback.of_right' (hpb O) hpbU
  have hQp : ∀ O, _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (q O)) := fun O => by
    have := hVaff O
    have := hWaff O
    infer_instance
  obtain ⟨Y₀, e, P, hP, hQP⟩ := exists_representing_over_of_openCover_of_size_le B S hS
    isZariskiLocalAtTarget_isAffineHom
    (BigFppfOver.isSheaf_pullback_yoneda_obj π a hF hY.isSheaf) (pullback.snd π a)
    hu (fun y => by
      have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hy
      obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨O, by rw [hurange O]; exact hO⟩)
    hpb' hQp hμ hWsize
  -- so `F ×_Y U ⟶ U` is representable and affine
  have hV : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd π a) := by
    have h1 : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map P) :=
      (presheaf_yoneda_map_iff B S hS inferInstance P).2 hQP
    have h2 : pullback.snd π a = e.hom ≫ yoneda.map P := by
      rw [← hP, Iso.hom_inv_id_assoc]
    rw [h2]
    exact MorphismProperty.RespectsIso.precomp _ e.hom _ h1
  exact isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hF hY hs he hV

/-- The hypothesis over all affine étale charts of `X` gives the hypothesis over the affine opens
of any atlas: an affine open `V ⟶ U` of an atlas `a : U ⟶ X`, composed with `a`, is an affine
étale chart of `X`. -/
theorem exists_isPullback_of_affineChart {X : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : F ⟶ X.1) {μ : Cardinal.{u}}
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      ∃ (W : BigAffineFppf B S hS) (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
        (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.obj.left),
        IsPullback p (yoneda.map q) π V.obj.hom ∧
          ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W)).size ≤ μ)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X.1}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (V : BigFppfOver B S hS) (u : V ⟶ U)
    (hu : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F) (q : W ⟶ V),
      IsPullback p (yoneda.map q) π (yoneda.map u ≫ a) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ := by
  have hchart : IsEtaleChart B S hS X.1 (CostructuredArrow.mk (yoneda.map u ≫ a)) :=
    etale_comp_of_scheme B S hS u a inferInstance he
  obtain ⟨W, p, q, hpb, hsize⟩ := h ⟨CostructuredArrow.mk (yoneda.map u ≫ a), hchart⟩ hV
  exact ⟨(BigAffineFppf.inclusion B S hS).obj W, p, q, hpb, W.property, hsize⟩

/-- **A sheaf over an algebraic space `X` which is a bounded affine scheme over every affine
étale chart of `X` is an algebraic space, and is affine over `X`.**

Let `π : F ⟶ X` be a morphism from an fppf sheaf to an algebraic space.  If for every affine
étale chart `V` of `X` the base change of `π` to `V` is represented by an affine object `W_V` of
the site, the sizes of the `W_V` being bounded by one cardinal `μ` below the cutoff, then `F` is
an algebraic space and `π` is affine (Stacks 03WF).

The bound `μ` cannot be dropped: see the implementation notes of this file for a sheaf satisfying
the remaining hypotheses which is not an algebraic space. -/
theorem isAlgebraicSpace_and_isAffineHom_of_affineChart {X : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ X.1)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      ∃ (W : BigAffineFppf B S hS) (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
        (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.obj.left),
        IsPullback p (yoneda.map q) π V.obj.hom ∧
          ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W)).size ≤ μ) :
    IsAlgebraicSpace B S hS F ∧ IsAffineHom B S hS π := by
  obtain ⟨U, a, hs, he⟩ := X.2.exists_atlas
  obtain ⟨hFalg, hπ⟩ := isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas B S hS X.2 hF π hs he
    hμ (exists_isPullback_of_affineChart B S hS π h he)
  exact ⟨hFalg, isAffineHom_of_presheaf hπ⟩

/-- **A sheaf over an algebraic space `X` which is a bounded affine scheme over every affine
étale chart of `X` is an algebraic space.**  The algebraicity half of
`AlgebraicGeometry.Space.isAlgebraicSpace_and_isAffineHom_of_affineChart`. -/
theorem isAlgebraicSpace_of_affineChart {X : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ X.1)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      ∃ (W : BigAffineFppf B S hS) (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
        (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.obj.left),
        IsPullback p (yoneda.map q) π V.obj.hom ∧
          ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W)).size ≤ μ) :
    IsAlgebraicSpace B S hS F :=
  (isAlgebraicSpace_and_isAffineHom_of_affineChart B S hS hF π hμ h).1

end AlgebraicGeometry.Space

end
