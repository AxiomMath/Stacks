module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# The base change of an étale chart of a formal algebraic space along a scheme-valued point

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` and let `c : T' ⟶ X` be a morphism from an object of the site. The existence half of the
proof of **Stacks 0AQD** starts by choosing an affine formal algebraic space `U` with an étale
morphism `U ⟶ X` and forming `V = U ×_{X, c} T'`, "an étale and separated morphism of schemes"
over `T'`. This file supplies that step.

* `V` is an object of the site because the chart is representable by schemes, **Stacks 0AIG**
  in the form `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isEtale_of_isAffineFormal`.
* `V ⟶ T'` is étale because the chart is.
* `V ⟶ T'` is separated because every morphism out of an affine formal algebraic space is
  separated (`AlgebraicGeometry.FormalSpace.isSeparatedMorphism_of_isAffineFormalAlgebraicSpace`),
  separatedness is stable under base change, and for a morphism of the site separatedness of
  the represented morphism of sheaves is separatedness of the morphism of schemes.
* Every point of `T'` is in the image of `V ⟶ T'` for some member of the atlas of
  Definition 0AIM, because the atlas is jointly locally surjective.

The source instead picks one chart whose image contains the image of `c`. That needs a finite
subcover and a finite coproduct of charts. Here each atlas member is used separately and the
resulting étale neighbourhoods are glued later.

## Main results

* `AlgebraicGeometry.FormalSpace.isSeparated_toScheme_map_of_isSeparatedMorphism`: separatedness
  of `fppfYoneda.map p` as a morphism of sheaves gives separatedness of the morphism of schemes
  underlying `p`.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_etale_isSeparated_of_chart`: the base change
  of one étale chart out of an affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_etale_isSeparated_mem_range`: for every point
  of `T'` some atlas member has a base change whose image contains it.

## References

* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0APX](https://stacks.math.columbia.edu/tag/0APX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism `p` of the big fppf site of `S`, separatedness of the represented morphism
of fppf sheaves gives separatedness of the underlying morphism of schemes. The sheafified Yoneda
embedding and the functor to schemes both preserve fibre products, so the relative diagonal of
`fppfYoneda.map p` is the image of the diagonal of `p`, and the closed immersion condition on
its represented base changes reads off at the diagonal of `p` itself. -/
theorem isSeparated_toScheme_map_of_isSeparatedMorphism {V T : BigFppfOver B S hS}
    (p : V ⟶ T) (hp : IsSeparatedMorphism B S hS ((fppfYoneda B S hS).map p)) :
    AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let Y := fppfYoneda B S hS
  let T := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan Y :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  let : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  have hsq : IsPullback (𝟙 (Y.obj V)) (Y.map (pullback.diagonal p))
      (pullback.diagonal (Y.map p)) (pullbackComparison Y p p) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    refine pullback.hom_ext ?_ ?_ <;> simp [← Y.map_comp]
  have hΔ : AlgebraicGeometry.IsClosedImmersion (T.map (pullback.diagonal p)) :=
    ((isSeparatedMorphism_iff_hasRelativeDiagonal B S hS (Y.map p)).mp hp).property _ _ _ hsq
  have hfac : T.map (pullback.diagonal p) ≫ pullbackComparison T p p =
      pullback.diagonal (T.map p) := by
    refine pullback.hom_ext ?_ ?_ <;> simp [← T.map_comp]
  refine ⟨?_⟩
  rw [← hfac]
  infer_instance

/-- **The base change of one étale chart along a scheme-valued point.** Let `u : U ⟶ X` be a
morphism of fppf sheaves out of an affine formal algebraic space which is representable by
algebraic spaces and étale, and let `c` be a morphism to `X` from the sheaf represented by an
object `T'` of the site. Then the fibre product `U ×_X T'` is represented by an object `V` of the
site, and the projection `p : V ⟶ T'` is étale and separated as a morphism of schemes. -/
theorem exists_isPullback_etale_isSeparated_of_chart {X U : FppfSheaf B S hS} (u : U ⟶ X)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS u.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) u.hom hrep)
    {T' : BigFppfOver B S hS} (c : (fppfYoneda B S hS).obj T' ⟶ X) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ T') (q : (fppfYoneda B S hS).obj V ⟶ U),
      IsPullback q ((fppfYoneda B S hS).map p) u c ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := fppfYoneda B S hS
  let K := sheafToPresheaf J (Type (u + 1))
  let gl : F ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  have hrepU := relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS u hU hrep het
  let ξ : uliftYoneda.{u + 1}.obj T' ⟶ X.obj := gl.inv.app T' ≫ c.hom
  obtain ⟨V, p, q₀, hsq⟩ := hrepU ξ
  let q : F.obj V ⟶ U := K.preimage (gl.hom.app V ≫ q₀)
  have hKq : K.map q = gl.hom.app V ≫ q₀ := K.map_preimage _
  have hpre : IsPullback (K.map q) (K.map (F.map p)) (K.map u) (K.map c) := by
    refine hsq.of_iso (gl.symm.app V) (Iso.refl _) (gl.symm.app T') (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hKq]
    · exact gl.inv.naturality p
    · simp [K]
    · simp [ξ, K]
  have hw : q ≫ u = F.map p ≫ c := K.map_injective (by simpa using hpre.w)
  have sq := IsPullback.of_map K hw hpre
  refine ⟨V, p, q, sq, ?_, ?_⟩
  · -- étale, from the étale base change of the chart
    have hhold := holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
      (@AlgebraicGeometry.Etale.{u}) (fun _ hk ↦ hk) (pullback.fst ξ u.hom) (het T' ξ)
    have hP : ∀ ⦃A C : BigFppfOver B S hS⦄ (k : A ⟶ C), IsIso k →
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) k := by
      intro A C k hk
      change Etale ((BigFppfOver.toScheme B S hS).map k)
      infer_instance
    exact hhold V T' hsq.flip.isoPullback.hom (𝟙 _) p
      (relative_of_isIso B S hS _ hP _) (relative_of_isIso B S hS _ hP _)
      (by rw [Category.comp_id, IsPullback.isoPullback_hom_fst])
  · -- separated, by base change from the chart
    exact isSeparated_toScheme_map_of_isSeparatedMorphism B S hS p
      (isSeparatedMorphism_of_isPullback B S hS sq
        (isSeparatedMorphism_of_isAffineFormalAlgebraicSpace B S hS u hU))

/-- **Every point of a scheme-valued point is reached by the base change of an atlas member.**
Let `X` be a formal algebraic space over `S`, let `c` be a morphism to `X` from the sheaf
represented by an object `T'` of the site, and let `t` be a point of the scheme underlying
`T'`. Then some affine formal algebraic space `U` mapping to `X` has a base change `V ⟶ T'`
along `c`, represented by an object of the site, which is étale and separated as a morphism of
schemes and contains `t` in its image.

The atlas of Definition 0AIM is jointly locally surjective, so over some arrow `Z ⟶ T'` of an
fppf covering sieve whose image contains `t` the point `c` lifts to an atlas member; that arrow
factors through the base change of that member. -/
theorem exists_isPullback_etale_isSeparated_mem_range {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {T' : BigFppfOver B S hS}
    (c : (fppfYoneda B S hS).obj T' ⟶ X) (t : (BigFppfOver.toScheme B S hS).obj T') :
    ∃ (U : FppfSheaf B S hS) (u : U ⟶ X) (V : BigFppfOver B S hS) (p : V ⟶ T')
      (q : (fppfYoneda B S hS).obj V ⟶ U),
      IsAffineFormalAlgebraicSpace B S hS U ∧ IsPullback q ((fppfYoneda B S hS).map p) u c ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map p) := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : (fppfYoneda B S hS).Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : (fppfYoneda B S hS).Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, g, haff, het, hsurj⟩ := hX
  have hR := family_imageSieve_mem J Xi X g hsurj T' (Sheaf.sectionEquiv J c)
  obtain ⟨Z, h, hRh, z, hz⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hR t
  obtain ⟨_, ⟨i, rfl⟩, s, hs⟩ := (Sieve.sSup_apply h).1 hRh
  obtain ⟨hrep, hetale⟩ := het i
  obtain ⟨V, p, q, sq, hpe, hps⟩ :=
    exists_isPullback_etale_isSeparated_of_chart B S hS (g i) (haff i) hrep hetale c
  have hlift : (Sheaf.sectionEquiv J).symm s ≫ g i = (fppfYoneda B S hS).map h ≫ c := by
    apply (Sheaf.sectionEquiv J).injective
    rwa [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply, Sheaf.sectionEquiv_map_comp]
  let ℓ : Z ⟶ V := (fppfYoneda B S hS).preimage (sq.lift _ _ hlift)
  have hℓ : ℓ ≫ p = h := by
    apply (fppfYoneda B S hS).map_injective
    rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd]
  refine ⟨Xi i, g i, V, p, q, haff i, sq, hpe, hps, (BigFppfOver.toScheme B S hS).map ℓ z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hℓ]

end AlgebraicGeometry.FormalSpace

end
