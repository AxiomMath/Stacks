module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlasRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts

/-!
# The set-theoretic condition descends along a representable morphism

Let `S` be a scheme contained in a big fppf site `B` and let `g : X ⟶ Y` be a morphism of fppf
sheaves over `S` which is representable by algebraic spaces. If `Y` satisfies the set-theoretic
condition of **Stacks 0AIS** then so does `X`.

This is what makes the condition usable. It is *not* automatic — it is false for a morphism
which is not representable: the colimit of `Spec R[x_t : t ∈ T]/(x_s x_t)` over the sets `T` of
cardinality below the size cutoff of the site is a directed system of thickenings of affine
schemes of the site whose colimit admits no surjection from an object of the site at all, and
it maps to `Spec R`, which does. That map is not representable by algebraic spaces, and
representability is exactly what the argument below consumes.

## The argument

The condition on `Y` gives an object `U` of the site with a surjection `t : U ⟶ Y` of sheaves
and an object `R` of the site with a surjection `r : R ⟶ U ×_Y U`.

*The surjection onto `X`.* Put `P = U ×_Y X`. Its projection to `U` is a base change of `g`,
hence representable by algebraic spaces, and `U` is an algebraic space over `S`, so `P` is an
algebraic space over `S` by **Stacks 03XY**. Its étale scheme atlas (Definition **025Y**) is an
object `R₁` of the site surjecting onto `P`, and the projection `P ⟶ X` is a base change of `t`,
hence a surjection. The composite `a : R₁ ⟶ X` is the required surjection.

*The surjection onto the kernel pair.* Write `K = R₁ ×_X R₁`, `A = P ×_X P` and
`D = R₁ ×_X P`. The maps `K ⟶ D ⟶ A` are two base changes of the atlas `R₁ ⟶ P`, which is
representable by algebraic spaces because `P` is an algebraic space; and `A ⟶ U ×_Y U` is a base
change of `g`, because `A = (U ×_Y U) ×_Y X`
(the chart-relation square, proved in place). So `K ⟶ U ×_Y U` is representable by
algebraic spaces, and the fibre product `W = R ×_{U ×_Y U} K` is an algebraic space over `S`
lying over the algebraic space `R` and surjecting onto `K`, since `r` does onto `U ×_Y U`. The
étale scheme atlas of `W` is the required object of the site.

Only the *second* half of the condition on `Y` is doing work that the representability of the
diagonal of `Y` would otherwise do. That is the point of the second half: it is the weak
substitute for **Stacks 0AIP**, which this library has for an affine formal algebraic space
only.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace`:
  a scheme-valued point of an algebraic space over `S` is representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_of_representable`:
  **Stacks 03XY** for fppf sheaves over `S`.
* `AlgebraicGeometry.FormalSpace.exists_representable_epi_of_representable_over`: the first half
  of the condition for the source of a morphism representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_representable_over`: the
  transfer itself.

## Implementation notes

The statement is not registered on Stacks 0AIS. Its hypothesis is the condition for another
sheaf, and the tag's own observations are registered elsewhere
(`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`); what this
module is for is the removal of hypotheses from the consumers, which is where the tags are.

Representability of a scheme-valued point of an algebraic space is the representability of the
diagonal of that algebraic space, read through
`CategoryTheory.Functor.relativelyRepresentable.of_diag`, and is therefore representability by
*objects of the site*; it is weakened to representability by algebraic spaces at once, that
being the form in which base change and composition are available here.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.SetTheoreticDescent

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A scheme-valued point of an algebraic space over `S` is representable by algebraic
spaces.** The diagonal of an algebraic space is relatively representable, and for a full functor
preserving binary products and fibre products that is equivalent to relative representability of
every morphism out of a representable; a relatively representable morphism has represented base
changes, and a universe-lifted representable presheaf is an algebraic space. -/
theorem isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F)
    {R : BigFppfOver B S hS} (α : (uliftYoneda.{u + 1}).obj R ⟶ F) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS α := by
  intro T ξ
  obtain ⟨V, snd, fst, hpb⟩ :=
    Functor.relativelyRepresentable.of_diag hF.diagonal_representable α ξ
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback ξ α))
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V)

/-- **Stacks 03XY for fppf sheaves over `S`.** The fibre product of a morphism representable by
algebraic spaces with a morphism whose source is an algebraic space over `S` is an algebraic
space over `S`: the projection to that source is a base change of the representable morphism.
This is `AlgebraicGeometry.Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift`
transported from the chosen fibre product of presheaves to that of sheaves. -/
theorem isAlgebraicSpaceULift_pullback_of_representable {X Y Z : FppfSheaf B S hS} (g : X ⟶ Y)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom) (t : Z ⟶ Y)
    (hZ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback t g).obj :=
  Space.isAlgebraicSpaceULift_of_iso B S hS
    (PreservesPullback.iso (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      t g).symm
    (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS g.hom t.hom hg hZ)

/-- **The étale scheme atlas of an algebraic space over `S` is a surjection of fppf sheaves.**
The atlas of Definition 025Y is surjective and étale, hence locally surjective (Stacks 05VM). -/
theorem exists_epi_uliftYoneda_of_isAlgebraicSpaceULift {A : FppfSheaf B S hS}
    (hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS A.obj) :
    ∃ (R : BigFppfOver B S hS)
      (α : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R ⟶ A), Epi α := by
  obtain ⟨R, a, hsurj, hetale⟩ := hA.exists_atlas
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a :=
    isLocallySurjective_of_surjective_etale_uliftYoneda (hS := hS) (S := S) (B := B)
      (f := a) (hs := hsurj) (he := hetale)
  refine ⟨R,
    ⟨((BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.{u + 1}.app R).hom ≫ a⟩, ?_⟩
  rw [← Sheaf.isLocallySurjective_iff_epi]
  exact Presheaf.isLocallySurjective_comp _ _ a

/-- **A morphism representable by algebraic spaces whose target receives a surjection from an
algebraic space receives a surjection from an object of the site.** -/
theorem exists_epi_uliftYoneda_of_epi_of_representable {K E Z : FppfSheaf B S hS} (γ : K ⟶ E)
    (hγ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS γ.hom) (r : Z ⟶ E)
    (hr : Epi r) (hZ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj) :
    ∃ (R : BigFppfOver B S hS)
      (ω : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R ⟶ K), Epi ω := by
  obtain ⟨R, ω, _⟩ := exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS
    (isAlgebraicSpaceULift_pullback_of_representable B S hS γ hγ r hZ)
  have := Sheaf.epi_pullback_snd r γ hr
  exact ⟨R, ω ≫ pullback.snd r γ, inferInstance⟩

/-- A fppf sheaf isomorphic to a representable presheaf is an algebraic space over `S`. -/
private theorem isAlgebraicSpaceULift_of_iso_uliftYoneda {Z : FppfSheaf B S hS}
    {T : BigFppfOver B S hS} (e : Z.obj ≅ (uliftYoneda.{u + 1}).obj T) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj :=
  Space.isAlgebraicSpaceULift_of_iso B S hS e.symm
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)

/-- **The first half of the set-theoretic condition descends along a representable morphism.**
If `g : X ⟶ Y` is a morphism of fppf sheaves over `S` representable by algebraic spaces and `Y`
satisfies the set-theoretic condition of Stacks 0AIS, then there is an object `R₁` of the big
fppf site of `S` and a surjection of fppf sheaves onto `X` from the sheaf it represents.

The fibre product `P` of `X` with a surjection onto `Y` from a representable sheaf is an
algebraic space over `S` by **Stacks 03XY**, its projection to that sheaf being a base change of
`g`; the étale scheme atlas of `P` (Definition **025Y**) is an object of the site surjecting onto
it, and the projection `P ⟶ X` is a base change of a surjection. -/
theorem exists_representable_epi_of_representable_over {X Y : FppfSheaf B S hS} (g : X ⟶ Y)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hY : SatisfiesSetTheoreticCondition B S hS Y) :
    ∃ (R₁ : BigFppfOver B S hS)
      (a : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R₁ ⟶ X), Epi a := by
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, t, ht, -⟩ := hY
  exact exists_epi_uliftYoneda_of_epi_of_representable B S hS g hg t ht
    (isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS eU)

/-- **The chart-relation square.** If `P = U ×_Y X`, then `P ×_X P` is the fibre product of the
kernel pair `U ×_Y U` with `X` over `Y`. -/
theorem isPullback_lift_of_kernelPair {C : Type*} [Category* C]
    {U X Y P A E : C} {t : U ⟶ Y} {g : X ⟶ Y} {p₁ : P ⟶ U} {p₂ : P ⟶ X}
    {a₁ a₂ : A ⟶ P} {e₁ e₂ : E ⟶ U} {c : A ⟶ E}
    (hV : IsPullback p₁ p₂ t g) (hA : IsPullback a₁ a₂ p₂ p₂) (hE : IsPullback e₁ e₂ t t)
    (hc₁ : c ≫ e₁ = a₁ ≫ p₁) (hc₂ : c ≫ e₂ = a₂ ≫ p₁) :
    IsPullback c (a₁ ≫ p₂) (e₁ ≫ t) g := by
  have hw : c ≫ e₁ ≫ t = (a₁ ≫ p₂) ≫ g := by
    rw [← Category.assoc, hc₁, Category.assoc, hV.w, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ hA.lift
    (hV.lift (s.fst ≫ e₁) s.snd (by simpa only [Category.assoc] using s.condition))
    (hV.lift (s.fst ≫ e₂) s.snd (by
      rw [Category.assoc, ← hE.w, ← Category.assoc]
      simpa only [Category.assoc] using s.condition))
    (by rw [hV.lift_snd, hV.lift_snd])) ?_ ?_ ?_⟩⟩
  · intro s
    refine hE.hom_ext ?_ ?_
    · rw [Category.assoc, hc₁, ← Category.assoc, hA.lift_fst, hV.lift_fst]
    · rw [Category.assoc, hc₂, ← Category.assoc, hA.lift_snd, hV.lift_fst]
  · intro s
    rw [← Category.assoc, hA.lift_fst, hV.lift_snd]
  · intro s m hm₁ hm₂
    refine hA.hom_ext ?_ ?_
    · rw [hA.lift_fst]
      refine hV.hom_ext ?_ ?_
      · rw [hV.lift_fst, Category.assoc, ← hc₁, ← Category.assoc, hm₁]
      · rw [hV.lift_snd, Category.assoc, hm₂]
    · rw [hA.lift_snd]
      refine hV.hom_ext ?_ ?_
      · rw [hV.lift_fst, Category.assoc, ← hc₂, ← Category.assoc, hm₁]
      · rw [hV.lift_snd, Category.assoc, ← hA.w, hm₂]

/-- Representability by algebraic spaces of a morphism of fppf sheaves is stable under base
change. -/
private theorem isRepresentableByAlgebraicSpacesULift_of_isPullback_sheaf
    {F G G' H : FppfSheaf B S hS} {p : H ⟶ F} {a' : H ⟶ G'} {a : F ⟶ G} {g : G' ⟶ G}
    (h : IsPullback a' p g a)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a'.hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS p.hom a'.hom a.hom g.hom
    (h.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) ha

/-- **The kernel pair of a chart of `U ×_Y X` maps representably to that of `U ⟶ Y`.** If `g`
is representable by algebraic spaces and `β : V ⟶ U ×_Y X` is, then the kernel pair of
`V ⟶ X` maps to `U ×_Y U` by a morphism representable by algebraic spaces: it factors through
`V ×_X P` and `P ×_X P`, two base changes of `β`, followed by a base change of `g`. -/
theorem exists_representable_kernelPair_hom {X Y U V : FppfSheaf B S hS} (g : X ⟶ Y)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom) (t : U ⟶ Y)
    (β : V ⟶ pullback t g)
    (hβ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS β.hom) :
    ∃ γ : pullback (β ≫ pullback.snd t g) (β ≫ pullback.snd t g) ⟶ pullback t t,
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS γ.hom := by
  let P := pullback t g
  let p₁ : P ⟶ U := pullback.fst t g
  let p₂ : P ⟶ X := pullback.snd t g
  have hV : IsPullback p₁ p₂ t g := IsPullback.of_hasPullback t g
  let a : V ⟶ X := β ≫ p₂
  let E := pullback t t
  let e₁ : E ⟶ U := pullback.fst t t
  let e₂ : E ⟶ U := pullback.snd t t
  have hE : IsPullback e₁ e₂ t t := IsPullback.of_hasPullback t t
  let A := pullback p₂ p₂
  let a₁ : A ⟶ P := pullback.fst p₂ p₂
  let a₂ : A ⟶ P := pullback.snd p₂ p₂
  have hA : IsPullback a₁ a₂ p₂ p₂ := IsPullback.of_hasPullback p₂ p₂
  let D := pullback a p₂
  let d₁ : D ⟶ V := pullback.fst a p₂
  let d₂ : D ⟶ P := pullback.snd a p₂
  have hD : IsPullback d₁ d₂ (β ≫ p₂) p₂ := IsPullback.of_hasPullback a p₂
  have hcomm : (a₁ ≫ p₁) ≫ t = (a₂ ≫ p₁) ≫ t := by
    simpa only [Category.assoc, hV.w] using hA.w =≫ g
  let c : A ⟶ E := hE.lift (a₁ ≫ p₁) (a₂ ≫ p₁) hcomm
  have hc : IsPullback c (a₁ ≫ p₂) (e₁ ≫ t) g :=
    isPullback_lift_of_kernelPair hV hA hE (hE.lift_fst _ _ hcomm) (hE.lift_snd _ _ hcomm)
  have hcrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom :=
    isRepresentableByAlgebraicSpacesULift_of_isPullback_sheaf B S hS hc hg
  obtain ⟨v, hsq₂⟩ : ∃ v : D ⟶ A, IsPullback v d₁ a₁ β :=
    ⟨_, IsPullback.of_right' hD.flip hA.flip⟩
  obtain ⟨w, hsq₁⟩ : ∃ w : pullback a a ⟶ D, IsPullback w (pullback.snd a a) d₂ β :=
    ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback a a) hD⟩
  have hvrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS v.hom :=
    isRepresentableByAlgebraicSpacesULift_of_isPullback_sheaf B S hS hsq₂ hβ
  have hwrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom :=
    isRepresentableByAlgebraicSpacesULift_of_isPullback_sheaf B S hS hsq₁ hβ
  exact ⟨w ≫ v ≫ c, Space.isRepresentableByAlgebraicSpacesULift_comp B S hS w.hom (v ≫ c).hom
    hwrep (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS v.hom c.hom hvrep hcrep)⟩

/-- **The set-theoretic condition of Stacks 0AIS descends along a morphism representable by
algebraic spaces.** If `g : X ⟶ Y` is a morphism of fppf sheaves on the big fppf site of `S`
which is representable by algebraic spaces and `Y` satisfies the condition, then so does `X`.

The surjection onto `X` is
`AlgebraicGeometry.FormalSpace.exists_representable_epi_of_representable_over`. Its kernel pair
`K = R₁ ×_X R₁` maps to the kernel pair `U ×_Y U` of the given surjection onto `Y` by a morphism
representable by algebraic spaces: it factors through `R₁ ×_X P` and `P ×_X P`, each step a base
change of the atlas `R₁ ⟶ P` — representable because `P` is an algebraic space — and
`P ×_X P ⟶ U ×_Y U` is a base change of `g`, that fibre product being `(U ×_Y U) ×_Y X`. The
fibre product of `K` with the given surjection onto `U ×_Y U` is therefore an algebraic space
over `S` surjecting onto `K`, and its étale scheme atlas is an object of the site surjecting
onto `K`. -/
theorem satisfiesSetTheoreticCondition_of_representable_over {X Y : FppfSheaf B S hS} (g : X ⟶ Y)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hY : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, t, ht, r₀, hr₀⟩ := hY
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback t g).obj :=
    isAlgebraicSpaceULift_pullback_of_representable B S hS g hg t
      (isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS eU)
  obtain ⟨R₁, β, _⟩ := exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS hPalg
  obtain ⟨γ, hγ⟩ := exists_representable_kernelPair_hom B S hS g hg t β
    (isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace B S hS hPalg β.hom)
  obtain ⟨R₂, ω, hω⟩ := exists_epi_uliftYoneda_of_epi_of_representable B S hS γ hγ r₀ hr₀
    (isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS eR)
  have := Sheaf.epi_pullback_snd t g ht
  exact ⟨R₁, R₂, J.uliftYoneda.{u + 1}.obj R₁, J.uliftYoneda.{u + 1}.obj R₂,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R₁⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R₂⟩,
    β ≫ pullback.snd t g, epi_comp _ _, ω, hω⟩

end AlgebraicGeometry.FormalSpace.SetTheoreticDescent

end
