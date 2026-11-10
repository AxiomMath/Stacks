module

public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Monomorphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a *monomorphism* when it is an
injective map of sheaves on the big fppf site of `S`, that is, a monomorphism of the
category of those sheaves. Since a morphism of algebraic spaces is a natural
transformation of presheaves, this is Mathlib's `CategoryTheory.Mono`, and the two
soriteses of the source — stability under composition and under base change — are its
general categorical counterparts.

This file proves the three assertions of the source which are specific to algebraic spaces:
that monomorphy of a morphism of algebraic spaces may equivalently be read in the category
of algebraic spaces or off the relative diagonal, that monomorphy is local on the target and
may be tested on affine schemes, and that an immersion is a monomorphism and therefore
separated.

## Main results

* `AlgebraicGeometry.Space.mono_hom_iff_mono` and
  `AlgebraicGeometry.Space.mono_iff_isIso_diagonal`: **Stacks 042M**, the three readings of
  monomorphy of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.mono_tfae`: **Stacks 042Q**, monomorphy is local on the target.
* `AlgebraicGeometry.Space.mono_of_isImmersion` and
  `AlgebraicGeometry.Space.isSeparated_of_isImmersion`: **Stacks 042R**, an immersion is a
  monomorphism, and is separated.

## Implementation notes

Taking `CategoryTheory.Mono` as the definition rather than introducing a predicate makes
both formulations of the source available at once: `Mono f` for a natural transformation
`f` is equivalent to injectivity of each of its components, by
`CategoryTheory.NatTrans.mono_iff_mono_app`. Downstream statements use `[Mono f]`.

The equivalence of the three conditions of Tag 042M is read off two cartesian squares. In the
category of algebraic spaces the relative diagonal of `f` is Mathlib's
`CategoryTheory.Limits.pullback.diagonal`, and `CategoryTheory.Limits.pullback.isIso_diagonal_iff`
is already the equivalence of conditions (2) and (3) there. For conditions (1) and (2) only
one implication is formal — the inclusion of the full subcategory is faithful, so it reflects
monomorphisms; the other uses that the presheaf fibre product of `f` with itself is a fibre
product in the category of algebraic spaces,
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, and that monomorphy of `f` is
equality of the two projections of any such square,
`CategoryTheory.mono_iff_fst_eq_snd`.

Locality on the target, Tag 042Q, rests on one statement of general site theory, recorded here
as a private lemma: if the source of `f : X ⟶ Y` is a sheaf, if a family `g i : V i ⟶ Y`
induces a locally surjective morphism out of the coproduct of the `V i`, and if every base
change of `f` along a `g i` is a monomorphism, then `f` is a monomorphism. Monomorphy of the
base changes makes `f` *locally* injective, which for a separated — in particular a sheaf —
source is injectivity. The three implications into condition (1) are that lemma applied to the
one-member family of a surjective étale chart, to a Zariski covering of the target, and to the
affine opens of a surjective étale chart. In the last case the chart contributes its own local
surjectivity, by
`AlgebraicGeometry.Space.isLocallySurjective_of_presheafSurjective_etale`, and the affine opens
contribute theirs, by `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`.
Condition (4) is phrased, following Tag 03ME and Tag 03FR, with surjectivity on points and
étaleness of charts; those are exchanged for the relatively representable properties the proof
consumes by `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda` and
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`.

Tag 042N, that a monomorphism of algebraic spaces is separated, is
`AlgebraicGeometry.Space.isSeparated_of_mono` in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalMonomorphism.lean`, where it is stated for
an arbitrary morphism of presheaves; it is not restated here. The separatedness half
of Tag 042R is proved directly from monomorphy of the immersion, since the relative diagonal of
a monomorphism is an isomorphism and an isomorphism of presheaves is a closed immersion in the
sense of `CategoryTheory.MorphismProperty.presheaf`.

Injectivity on points is Tag 06RV, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/PointsMono.lean` for an arbitrary morphism of presheaves
on the big fppf site; this file imports it rather than repeating it.

## References

* [Stacks Project, Tag 042L](https://stacks.math.columbia.edu/tag/042L)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 042O](https://stacks.math.columbia.edu/tag/042O)
* [Stacks Project, Tag 042P](https://stacks.math.columbia.edu/tag/042P)
* [Stacks Project, Tag 042Q](https://stacks.math.columbia.edu/tag/042Q)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-! ### Monomorphy of a morphism of presheaves is local on the target -/

section Site

variable {C : Type v} [Category.{u, v} C]

/-- A section of a coproduct of presheaves over an object `W` of the site comes from a single
summand, in the shape of a morphism out of the representable presheaf of `W`. -/
private theorem exists_factor_sigmaDesc {I : Type u} (V : I → Cᵒᵖ ⥤ Type u)
    {Y : Cᵒᵖ ⥤ Type u} (g : ∀ i, V i ⟶ Y) (W : C) (z : (∐ V).obj (op W)) :
    ∃ i, ∃ γ : yoneda.obj W ⟶ V i,
      (Sigma.desc g).app (op W) z = (g i).app (op W) (yonedaEquiv γ) := by
  let σ := sigmaObjIso V (op W)
  obtain ⟨i, zi, hzi⟩ := Cofan.inj_jointly_surjective_of_isColimit
    (colimit.isColimit (Discrete.functor fun i ↦ (V i).obj (op W))) (σ.hom z)
  have hz : z = (Sigma.ι V i).app (op W) zi := by
    refine (ConcreteCategory.bijective_of_isIso σ.hom).1 ?_
    calc
      σ.hom z = (colimit.ι (Discrete.functor fun i ↦ (V i).obj (op W)) ⟨i⟩) zi := hzi.symm
      _ = σ.hom ((Sigma.ι V i).app (op W) zi) :=
        (congrArg (fun q ↦ q zi) (ι_comp_sigmaObjIso_hom V (op W) i)).symm
  refine ⟨i, (yonedaEquiv (F := V i)).symm zi, ?_⟩
  rw [hz]
  change ((Sigma.ι V i ≫ Sigma.desc g).app (op W)) zi = _
  rw [Sigma.ι_comp_desc]
  simp

private theorem isLocallyInjective_of_isLocallySurjective_sigmaDesc (J : GrothendieckTopology C)
    {X Y : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) {I : Type u} (V : I → Cᵒᵖ ⥤ Type u) (g : ∀ i, V i ⟶ Y)
    (hcover : Presheaf.IsLocallySurjective J (Sigma.desc g))
    (hmono : ∀ i, Mono (pullback.snd f (g i))) : Presheaf.IsLocallyInjective J f := by
  refine ⟨fun {U} x y hxy ↦ ?_⟩
  refine J.superset_covering ?_ (hcover.imageSieve_mem (f.app U x))
  rintro W a ⟨z, hz⟩
  obtain ⟨i, γ, hfac⟩ := exists_factor_sigmaDesc V g W z
  let α : yoneda.obj W ⟶ X := (yonedaEquiv (F := X)).symm (X.map a.op x)
  let β : yoneda.obj W ⟶ X := (yonedaEquiv (F := X)).symm (X.map a.op y)
  have key (t : X.obj U) (ht : Y.map a.op (f.app U x) = Y.map a.op (f.app U t)) :
      (yonedaEquiv (F := X)).symm (X.map a.op t) ≫ f = γ ≫ g i := by
    apply (yonedaEquiv (F := Y)).injective
    simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [NatTrans.naturality_apply f a.op t]
    rw [← hfac, ← ht, ← hz]
  have hα : α ≫ f = γ ≫ g i := key x rfl
  have hβ : β ≫ f = γ ≫ g i := key y (by rw [hxy])
  have : Mono (pullback.snd f (g i)) := hmono i
  have heq : pullback.lift α γ hα = pullback.lift β γ hβ :=
    (cancel_mono (pullback.snd f (g i))).1 (by rw [pullback.lift_snd, pullback.lift_snd])
  have hαβ : α = β := (pullback.lift_fst α γ hα).symm.trans
    ((congrArg (· ≫ pullback.fst f (g i)) heq).trans (pullback.lift_fst β γ hβ))
  change X.map a.op x = X.map a.op y
  simpa [α, β] using congrArg (yonedaEquiv (F := X)) hαβ

/-- **Monomorphy is local on the target.** Let `f : X ⟶ Y` be a morphism of presheaves on a
site with sheaf source, and let `g i : V i ⟶ Y` be a family whose induced morphism out of the
coproduct of the `V i` is locally surjective. If every base change of `f` along a `g i` is a
monomorphism, then so is `f`.

Lifting two sections of `X` which agree under `f` to morphisms out of a representable presheaf
and factoring the common image through some `g i` exhibits the two lifts as morphisms into the
base change of `f` along `g i` with the same second component, so they agree. That makes `f`
locally injective, and the source being a sheaf turns local injectivity into injectivity. -/
@[sga "3 IV 4.5.7" "partial", sga "3 IV 4.5.8" "partial"]
private theorem mono_of_isLocallySurjective_sigmaDesc (J : GrothendieckTopology C)
    {X Y : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) {I : Type u} (V : I → Cᵒᵖ ⥤ Type u) (g : ∀ i, V i ⟶ Y)
    (hX : Presheaf.IsSheaf J X)
    (hcover : Presheaf.IsLocallySurjective J (Sigma.desc g))
    (hmono : ∀ i, Mono (pullback.snd f (g i))) : Mono f := by
  have hsep : Presieve.IsSeparated J (X ⋙ forget (Type u)) :=
    ((isSheaf_iff_isSheaf_of_type J X).1 hX).isSeparated
  refine (NatTrans.mono_iff_mono_app f).2 fun U ↦ (mono_iff_injective (f.app U)).2 ?_
  exact (Presheaf.isLocallyInjective_iff_injective_of_separated J f hsep).1
    (isLocallyInjective_of_isLocallySurjective_sigmaDesc J f V g hcover hmono) U

/-- A jointly surjective family of morphisms of a site, in the sense that it generates a
covering sieve, induces a locally surjective morphism out of the coproduct of the
representable presheaves of its sources. -/
private theorem isLocallySurjective_sigmaDesc_yoneda_map (J : GrothendieckTopology C)
    {I : Type u} (V : I → C) {T : C} (m : ∀ i, V i ⟶ T)
    (hcover : Sieve.ofArrows V m ∈ J T) :
    Presheaf.IsLocallySurjective J (Sigma.desc fun i ↦ yoneda.map (m i)) := by
  refine ⟨fun {W} z ↦ ?_⟩
  refine J.superset_covering ?_ (J.pullback_stable (z : W ⟶ T) hcover)
  intro W' a ha
  rw [Sieve.pullback_apply] at ha
  obtain ⟨i, b, hb⟩ := (Sieve.mem_ofArrows_iff V m (a ≫ (z : W ⟶ T))).mp ha
  refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (V i)) i).app (op W') b, ?_⟩
  change ((Sigma.ι (fun i ↦ yoneda.obj (V i)) i ≫
    Sigma.desc fun i ↦ yoneda.map (m i)).app (op W')) b = _
  rw [Sigma.ι_comp_desc]
  exact hb.symm

end Site

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Monomorphisms in the category of algebraic spaces -/

/-- **Stacks 042M, parts (1) and (2).** A morphism of algebraic spaces over `S` is a
monomorphism of the underlying presheaves exactly when it is a monomorphism of the category
of algebraic spaces over `S`. -/
@[stacks 042M "parts (1) and (2)"]
theorem mono_hom_iff_mono {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Mono f.hom ↔ Mono f := by
  refine ⟨fun h ↦ (ObjectProperty.ι _).mono_of_mono_map h, fun h ↦ ?_⟩
  have hfs : (ObjectProperty.homMk (pullback.fst f.hom f.hom) :
      AlgebraicSpaces.fiberProduct B S hS f f ⟶ X) =
      ObjectProperty.homMk (pullback.snd f.hom f.hom) :=
    (mono_iff_fst_eq_snd (AlgebraicSpaces.isPullback_fiberProduct B S hS f f).isLimit).1 h
  exact (mono_iff_fst_eq_snd (IsPullback.of_hasPullback f.hom f.hom).isLimit).2
    (congrArg (fun m ↦ m.hom) hfs)

/-- **Stacks 042M, parts (2) and (3).** A morphism of algebraic spaces over `S` is a
monomorphism of the category of algebraic spaces over `S` exactly when its relative diagonal
is an isomorphism. -/
@[stacks 042M "parts (2) and (3)", ega "I 5.3.8"]
theorem mono_iff_isIso_diagonal {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Mono f ↔ IsIso (pullback.diagonal f) :=
  (pullback.isIso_diagonal_iff f).symm

/-! ### Monomorphy is local on the target -/

/-- **Stacks 042Q.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are
equivalent: `f` is a monomorphism; every base change of `f` to a scheme of the site is a
monomorphism; every base change of `f` to an affine scheme of the site is a monomorphism; the
base change of `f` along some surjective étale chart of `Y` is a monomorphism; and the base
changes of `f` along the members of some Zariski covering of `Y` are monomorphisms. -/
@[stacks 042Q]
theorem mono_tfae {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      Mono f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y), Mono (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) → Mono (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧ Mono (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧ ∀ i, Mono (pullback.snd f (U i).ι))] := by
  tfae_have 1 → 2 := fun _ _ _ ↦ inferInstance
  tfae_have 2 → 3 := fun h Z g _ ↦ h Z g
  tfae_have 4 → 1 := by
    rintro ⟨V, g, hsurj, hetale, hmono⟩
    refine mono_of_isLocallySurjective_sigmaDesc (BigFppfOver.topology B S hS) f
      (fun _ : PUnit.{u + 1} ↦ yoneda.obj V) (fun _ ↦ g) hX.isSheaf ?_ fun _ ↦ hmono
    have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g :=
      isLocallySurjective_of_presheafSurjective_etale g
        ((presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).2 hsurj)
        ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hetale)
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Sigma.ι_comp_desc (fun _ : PUnit.{u + 1} ↦ g) PUnit.unit)
  tfae_have 1 → 5 := by
    intro hf
    refine ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY, fun _ ↦ ?_⟩
    have : Mono f := hf
    infer_instance
  tfae_have 5 → 1 := by
    rintro ⟨I, U, hcover, hmono⟩
    exact mono_of_isLocallySurjective_sigmaDesc (BigFppfOver.topology B S hS) f
      (fun i ↦ (U i).toFunctor) (fun i ↦ (U i).ι) hX.isSheaf hcover.2 hmono
  tfae_have 3 → 4 := by
    intro h3
    obtain ⟨V, g, hsurj, hetale⟩ := hY.exists_atlas
    choose W u hu hurange hWaff using
      fun U ↦ BigFppfOver.exists_affineOpen_restrict B S hS V U
    have hVcover : Sieve.ofArrows W u ∈ BigFppfOver.topology B S hS V := by
      refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS u hu fun x ↦ ?_
      have hx : x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj V).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hx
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨U, by rwa [hurange U]⟩
    have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Sigma.desc fun U ↦ yoneda.map (u U)) :=
      isLocallySurjective_sigmaDesc_yoneda_map _ W u hVcover
    have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g :=
      isLocallySurjective_of_presheafSurjective_etale g hsurj hetale
    have hfac : (Sigma.desc fun U ↦ yoneda.map (u U)) ≫ g =
        Sigma.desc fun U ↦ yoneda.map (u U) ≫ g :=
      Sigma.hom_ext _ _ fun _ ↦ by simp
    have : Mono f := by
      refine mono_of_isLocallySurjective_sigmaDesc (BigFppfOver.topology B S hS) f
        (fun U ↦ yoneda.obj (W U)) (fun U ↦ yoneda.map (u U) ≫ g) hX.isSheaf ?_
        fun U ↦ h3 (W U) _ (hWaff U)
      rw [← hfac]
      infer_instance
    exact ⟨V, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).1 hsurj,
      (isEtale_iff_presheaf_of_yoneda B S hS g).2 hetale, inferInstance⟩
  tfae_finish

/-! ### Immersions -/

/-- **Stacks 042R.** An immersion of algebraic spaces over `S` is a monomorphism: an immersion
of schemes is a monomorphism, and a morphism of presheaves all of whose represented base
changes are monomorphisms is a monomorphism. -/
@[stacks 042R "monomorphism"]
theorem mono_of_isImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsImmersion B S hS f) : Mono f := by
  have hP : MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ MorphismProperty.monomorphisms _ := by
    intro U V m hm
    have : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map m) := hm
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map m)))
  exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms f
    (MorphismProperty.relative_monotone (F := yoneda) hP f hf)

/-- **Stacks 042R.** An immersion of algebraic spaces over `S` is separated: it is a
monomorphism, so its relative diagonal is an isomorphism, and an isomorphism of presheaves is
a closed immersion. -/
@[stacks 042R "separatedness", ega "I 5.5.1" "(i) immersions"]
theorem isSeparated_of_isImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsImmersion B S hS f) : IsSeparated B S hS f := by
  have : Mono f := mono_of_isImmersion B S hS hf
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := by
    refine ⟨fun T ↦ ?_⟩
    change _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 T))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.presheaf_of_isIso _ (pullback.diagonal f)

end AlgebraicGeometry.Space

end
