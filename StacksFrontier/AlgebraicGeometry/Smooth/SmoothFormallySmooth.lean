module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Local lifts along a thickening, and formal smoothness of a smooth morphism

Let `f : X ⟶ S` be a morphism of schemes. Formal smoothness of `f`,
`Stacks.Smooth.FormallySmoothScheme`, asks that every square

```
T  --a--→ X
|         |
i         f
↓         ↓
T' --h--→ S
```

with `i : T ⟶ T'` a first-order thickening of affine schemes admit a diagonal filler. The
direction `locally of finite presentation + formally smooth → smooth` of
[Stacks Project, Tag 02H6] is `Stacks.Smooth.smooth_of_formallySmoothScheme`, and the converse
is proved there only for an affine morphism. This file carries out, for an arbitrary smooth
morphism, the two *local* halves of the Stacks proof of the converse: a filler exists over an
affine open neighbourhood of every point of `T'`, and a family of fillers that agrees on
overlaps glues to a global filler. Combining them needs a correction step that is not available
here (see the implementation notes), but they already combine when fillers are unique, which
gives formal smoothness of every étale morphism.

## Main results

* `Stacks.Smooth.isFirstOrderThickening_morphismRestrict`: a first-order thickening restricts to
  a first-order thickening over any open of the ambient scheme.
* `Stacks.Smooth.exists_lift_of_range_subset`: for `f` smooth and `T'` affine, the lifting
  problem has a solution as soon as `a` maps into a single affine open of `X` lying over an
  affine open of `S`.
* `Stacks.Smooth.exists_isAffineOpen_lift`: for `f` smooth, every point of `T'` has an affine
  open neighbourhood `V'` over which the lifting problem has a solution. This is step (I) of the
  Stacks proof.
* `Stacks.Smooth.exists_lift_of_isOpenCover`: solutions of the lifting problem over the members
  of an open cover of `T'` that agree on pairwise intersections glue to a global solution. This
  is the gluing step of the Stacks proof.
* `Stacks.Smooth.lift_unique`: for `f` formally unramified a solution of the lifting problem is
  unique.
* `Stacks.Smooth.formallySmoothScheme_of_formallyUnramified`: a smooth formally unramified
  morphism — that is, an étale morphism — is formally smooth, with no affineness assumption on
  the morphism. Also recorded as `Stacks.Smooth.formallySmoothScheme_of_etale` and, for an open
  immersion, `Stacks.Smooth.formallySmoothScheme_of_isOpenImmersion`.
* `Stacks.Smooth.FormallySmoothScheme.comp`: formal smoothness is stable under composition.

## Implementation notes

A thickening `i : T ⟶ T'` is a closed immersion with nilpotent kernel ideal sheaf, hence a
homeomorphism on points. Two consequences are used throughout. First, an open `V'` of `T'`
determines the open `i ⁻¹ᵁ V'` of `T` and the restricted thickening
`i ∣_ V' : (i ⁻¹ᵁ V' : Scheme) ⟶ V'`; that this is again a first-order thickening is
`Stacks.Smooth.isFirstOrderThickening_morphismRestrict`, proved by reading the kernel ideal
sheaf of `i ∣_ V'` off that of `i` with `AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal`.
Second, in `Stacks.Smooth.exists_isAffineOpen_lift` the open of `T'` over which a lift is
produced is cut out by pushing an open of `T` forward along `i`, which is legitimate because `i`
is an open map; this is how one arranges that `i ⁻¹ᵁ V'` map into a chosen affine open `W` of
`X` lying over a chosen affine open `V` of `S`. On such a `V'` both `V'` and `i ⁻¹ᵁ V'` are
affine — the latter because it is a closed subscheme of the affine `V'` — and the affine case
`Stacks.Smooth.formallySmoothScheme_of_formallySmooth` applies to `f.resLE V W`, which is smooth
because smoothness is Zariski-local at source and target. That last step is isolated as
`Stacks.Smooth.exists_lift_of_range_subset`; note that there the hypothesis that `V'` lie over
`V` is not needed, since a thickening is surjective on points and so `h` and `a ≫ f` have the
same image.

The gluing step is `AlgebraicGeometry.Scheme.Cover.glueMorphisms` for the open cover of `T'`.
Its compatibility hypothesis is phrased on `U j ⊓ U k` rather than on the pullback of the two
open immersions; the translation factors the pullback through the intersection with
`AlgebraicGeometry.IsOpenImmersion.lift`.

What is missing for the unrestricted equivalence of Tag 02H6 is the correction step, step (II)
of the Stacks proof: the local lifts of `Stacks.Smooth.exists_isAffineOpen_lift` need not agree
on overlaps, and to make them agree one must know that the sheaf of lifts is a *trivial* torsor
under `SheafHom(a^*Ω_{X/S}, I)`, where `I` is the kernel ideal of the thickening. The
ingredients of that argument are available:

* the torsor structure at ring level, in the form of the bijection between lifts into a
  square-zero extension and derivations, is `derivationToSquareZeroEquivLift`;
* the localization of a `Hom` module along a finitely presented module is
  `Module.FinitePresentation.isLocalizedModule_map`, which is what turns the local differences
  into a Čech cochain for the standard covering; and
* the vanishing of the first Čech cohomology of a module over a ring with respect to a family
  generating the unit ideal is `Stacks.RingTheory.CechAcyclicity.cech_exact`.

The fourth ingredient is the sheaf of relative differentials itself, and it too is available:
`Stacks.Smooth.cotangentSheaf` is `Ω_{X/S}` as an object of `AlgebraicGeometry.Scheme.Modules`
and `Stacks.Smooth.pullbackCotangentSheaf` is `a^*Ω_{X/S}`.

So what remains is one quantitative statement, the affine computation of `Ω` — Stacks Project,
Tag 01UM — in the form the Čech step consumes. Spelled out: for `f : X ⟶ S`, affine opens
`V ⊆ S` and `W ⊆ X` with `W ≤ f ⁻¹ᵁ V`, an affine scheme `T` and `a : T ⟶ X` with
`Set.range a.base ⊆ W`, writing `R = Γ(S, V)`, `B = Γ(X, W)`, `A = Γ(T, ⊤)` and `α : B →+* A`
for the induced map, an isomorphism of `A`-modules
`Γ(a^*Ω_{X/S}, ⊤) ≅ Ω[B⁄R] ⊗[B] A` carrying the pullback of the universal derivation of a
section to `d · ⊗ 1`, naturally in restriction to the basic opens of `T`.

That one statement closes the argument, as follows. Over a basic open of `T'` on which `a` maps
into `W`, lifts are the same thing as `R`-algebra maps `B ⟶ A'` lifting `B ⟶ A`, so they form a
torsor under `Derivation R B I ≃ Hom_A(Ω[B⁄R] ⊗[B] A, I)` by `derivationToSquareZeroEquivLift`;
the displayed isomorphism identifies that group with the sections of
`Hom(a^*Ω_{X/S}, 𝒞_{T/T'})`, which makes the group independent of the chart and so provides the
comparison of the chart of `j` with the chart of `k` over their overlap — the one thing the
chart description by itself cannot supply. `Ω[B⁄R]` is finitely presented because `R ⟶ B` is
smooth, so `Module.FinitePresentation.isLocalizedModule_map` makes those groups localize, the
differences of the local lifts become a Čech 1-cocycle, `cech_exact` writes it as a coboundary,
and correcting the local lifts by the resulting 0-cochain makes them agree, at which point
`Stacks.Smooth.exists_lift_of_isOpenCover` finishes. Nothing in that chain needs a single global
module over `Γ(T, ⊤)`, and nothing needs sheaf cohomology.

Tags 01V3 and 02G1 — finite presentation, respectively finite local freeness, of `Ω_{X/S}` —
are the statements usually quoted at this point. They are not proved here. In the shape
`SheafOfModules.IsFinitePresentation` they would not
be enough on their own: that class gives a local presentation over *some* covering of the site,
with no identification of sections over a basic open with a localization, so it would still have
to be combined with the affine dictionary for quasi-coherent sheaves. The displayed computation
is what is actually needed, and 01V3 and 02G1 would both be proved from it.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- A first-order thickening restricts to a first-order thickening over any open `V'` of the
ambient scheme: the restriction `i ∣_ V'` is again a closed immersion, because being a closed
immersion is Zariski-local at the target, and its kernel ideal sheaf is still square-zero,
because the ideal it cuts out on an affine open `V` of `V'` is the one `i` cuts out on the image
of `V` in `T'`. -/
theorem isFirstOrderThickening_morphismRestrict {T T' : Scheme.{u}} {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (V' : T'.Opens) :
    Thickenings.IsFirstOrderThickening (i ∣_ V') := by
  have hci : IsClosedImmersion i := hi.1
  refine ⟨IsZariskiLocalAtTarget.restrict hci V', Scheme.IdealSheafData.ext (funext fun V => ?_)⟩
  have h2 := congrArg
    (fun J : T'.IdealSheafData => J.ideal ⟨V'.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩) hi.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply] at h2 ⊢
  rwa [Scheme.ker_morphismRestrict_ideal]

/-- Restricting a morphism to a smaller open of the target is the same as restricting it to the
larger one and then including: for `e : W ≤ V'`, the square formed by `i ∣_ W`, `i ∣_ V'` and the
two inclusions commutes. -/
theorem morphismRestrict_comp_homOfLE {T T' : Scheme.{u}} (i : T ⟶ T') {W V' : T'.Opens}
    (e : W ≤ V') :
    (i ∣_ W) ≫ T'.homOfLE e = T.homOfLE (show i ⁻¹ᵁ W ≤ i ⁻¹ᵁ V' from fun _ hx => e hx) ≫
      (i ∣_ V') := by
  rw [← cancel_mono V'.ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- **Lifts along a thickening glue.** Let `i : T ⟶ T'` be a morphism of schemes and let `a`,
`h` present a lifting problem for `f : X ⟶ S`. Given an open cover `U` of `T'` together with a
solution `b j` of the restricted lifting problem over each `U j`, such that any two of them agree
on the intersection `U j ⊓ U k`, the lifting problem has a global solution.

This is the gluing step of the proof of [Stacks Project, Tag 02H6]; no thickening or affineness
hypothesis is needed, only that the `b j` are compatible. -/
theorem exists_lift_of_isOpenCover {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T')
    (a : T ⟶ X) (h : T' ⟶ S) {κ : Type*} (U : κ → T'.Opens)
    (hU : TopologicalSpace.IsOpenCover U) (b : ∀ j, (U j).toScheme ⟶ X)
    (hbf : ∀ j, b j ≫ f = (U j).ι ≫ h)
    (hba : ∀ j, (i ∣_ U j) ≫ b j = (i ⁻¹ᵁ U j).ι ≫ a)
    (hbb : ∀ j k, T'.homOfLE (inf_le_left : U j ⊓ U k ≤ U j) ≫ b j =
      T'.homOfLE (inf_le_right : U j ⊓ U k ≤ U k) ≫ b k) :
    ∃ g' : T' ⟶ X, g' ≫ f = h ∧ i ≫ g' = a := by
  have hcompat : ∀ j k, Limits.pullback.fst (U j).ι (U k).ι ≫ b j =
      Limits.pullback.snd (U j).ι (U k).ι ≫ b k := by
    intro j k
    rw [← cancel_epi (isPullback_opens_inf (U j) (U k)).isoPullback.hom]
    simpa using hbb j k
  have hι : ∀ j, (U j).ι ≫ (T'.openCoverOfIsOpenCover U hU).glueMorphisms b hcompat = b j :=
    fun j => (T'.openCoverOfIsOpenCover U hU).ι_glueMorphisms b hcompat j
  refine ⟨(T'.openCoverOfIsOpenCover U hU).glueMorphisms b hcompat,
    Scheme.Cover.hom_ext (T'.openCoverOfIsOpenCover U hU) _ _ fun j => ?_, Scheme.Cover.hom_ext
      (T.openCoverOfIsOpenCover (fun j => i ⁻¹ᵁ U j) (i.iSup_preimage_eq_top hU)) _ _ fun j => ?_⟩
  · show (U j).ι ≫ _ ≫ f = (U j).ι ≫ h
    rw [← Category.assoc, hι j, hbf j]
  · show (i ⁻¹ᵁ U j).ι ≫ i ≫ _ = (i ⁻¹ᵁ U j).ι ≫ a
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc, hι j, hba j]

/-- **Lifts along a thickening exist when the lifting problem fits in a single pair of charts.**
Let `f : X ⟶ S` be smooth and let `i : T ⟶ T'` be a first-order thickening with `T'` affine. If
the lifting problem presented by `a : T ⟶ X` and `h : T' ⟶ S` has `a` mapping into an affine
open `W` of `X` which maps into an affine open `V` of `S`, then it has a solution.

This is the affine case of [Stacks Project, Tag 02H6] applied to `f.resLE V W`: the restriction
is a smooth morphism of affine schemes, `T` is affine because it is a closed subscheme of the
affine `T'`, and `h` maps into `V` automatically, because `i` is surjective on points and so the
image of `h` is the image of `a ≫ f`. -/
theorem exists_lift_of_range_subset {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
    [IsAffine T'] (a : T ⟶ X) (h : T' ⟶ S) (hcomm : a ≫ f = i ≫ h) {V : S.Opens} {W : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V)
    (hran : Set.range a.base ⊆ (W : Set X)) :
    ∃ b : T' ⟶ X, b ≫ f = h ∧ i ≫ b = a := by
  have hci : IsClosedImmersion i := hi.1
  have hVa : IsAffine (V : Scheme.{u}) := hV
  have hWa : IsAffine (W : Scheme.{u}) := hW
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hranV : Set.range h.base ⊆ Set.range V.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨x₀, rfl⟩ := hi.isThickening.2 x
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    exact hWV (hran ⟨x₀, rfl⟩)
  have hsrc : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have htgt : IsZariskiLocalAtTarget (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hsm : AlgebraicGeometry.Smooth (f.resLE V W hWV) :=
    IsZariskiLocalAtSource.resLE hWV inferInstance
  have hfs : FormallySmoothScheme (f.resLE V W hWV) :=
    formallySmoothScheme_of_formallySmooth ((smooth_iff_of_isAffine _).mp hsm).1
  obtain ⟨b₀, hb₁, hb₂⟩ := hfs (T := T) (T' := T') inferInstance inferInstance i hi
    (IsOpenImmersion.lift W.ι a (by rwa [Scheme.Opens.range_ι]))
    (IsOpenImmersion.lift V.ι h hranV) (by
      rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
        IsOpenImmersion.lift_fac, ← Category.assoc, IsOpenImmersion.lift_fac, hcomm])
  refine ⟨b₀ ≫ W.ι, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hWV, ← Category.assoc, hb₁,
      IsOpenImmersion.lift_fac]
  · rw [← Category.assoc, hb₂, IsOpenImmersion.lift_fac]

/-- **Lifts along a thickening exist locally.** Let `f : X ⟶ S` be smooth, let
`i : T ⟶ T'` be a first-order thickening and let `a : T ⟶ X`, `h : T' ⟶ S` present a lifting
problem for `f`. Then every point of `T'` has an affine open neighbourhood `V'` over which the
restricted lifting problem has a solution.

This is step (I) of the proof of [Stacks Project, Tag 02H6]: one chooses affine opens
`V ⊆ S` and `W ⊆ X` with `W ≤ f ⁻¹ᵁ V` around the images of the given point and shrinks `V'` so
that `i ⁻¹ᵁ V'` maps into `W`, which puts the restricted problem in the situation of
`Stacks.Smooth.exists_lift_of_range_subset`. -/
theorem exists_isAffineOpen_lift {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
    (a : T ⟶ X) (h : T' ⟶ S) (hcomm : a ≫ f = i ≫ h) (t : T') :
    ∃ V' : T'.Opens, IsAffineOpen V' ∧ t ∈ V' ∧ ∃ b : (V' : Scheme.{u}) ⟶ X,
      b ≫ f = V'.ι ≫ h ∧ (i ∣_ V') ≫ b = (i ⁻¹ᵁ V').ι ≫ a := by
  have hci : IsClosedImmersion i := hi.1
  obtain ⟨t₀, rfl⟩ := hi.isThickening.2 t
  obtain ⟨V, hV, hsV⟩ : ∃ V : S.Opens, IsAffineOpen V ∧ f.base (a.base t₀) ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base (a.base t₀)))
        isOpen_univ
    exact ⟨V, hV, hsV⟩
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : X.Opens, IsAffineOpen W ∧ a.base t₀ ∈ W ∧ W ≤ f ⁻¹ᵁ V := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show a.base t₀ ∈ f ⁻¹ᵁ V from hsV)
        (f ⁻¹ᵁ V).isOpen
    exact ⟨W, hW, hxW, hWV⟩
  have homeo : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, hi.isThickening.2⟩
  set Ω : T'.Opens := ⟨i.base '' (a ⁻¹ᵁ W : Set T), homeo.isOpenMap _ (a ⁻¹ᵁ W).isOpen⟩
  obtain ⟨V', hV', htV', hV'le⟩ : ∃ V' : T'.Opens, IsAffineOpen V' ∧ i.base t₀ ∈ V' ∧ V' ≤ Ω := by
    obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'le⟩ :=
      T'.isBasis_affineOpens.exists_subset_of_mem_open (show i.base t₀ ∈ Ω from ⟨t₀, hxW, rfl⟩)
        Ω.isOpen
    exact ⟨V', hV', htV', hV'le⟩
  have hpre : i ⁻¹ᵁ V' ≤ a ⁻¹ᵁ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hV'le hx
    exact homeo.injective hxy ▸ hy
  have hV'a : IsAffine (V' : Scheme.{u}) := hV'
  obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_range_subset f
    (isFirstOrderThickening_morphismRestrict hi V') ((i ⁻¹ᵁ V').ι ≫ a) (V'.ι ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← morphismRestrict_ι, Category.assoc])
    hV hW hWV (by
      rintro y ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hpre x.2)
  exact ⟨V', hV', htV', b, hb₁, hb₂⟩

/-- **Lifts along a thickening are unique for a formally unramified morphism.** Two solutions of
the same lifting problem for a formally unramified `f` along a first-order thickening agree. -/
theorem lift_unique {X S T T' : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S} {b₁ b₂ : T' ⟶ X}
    (hb₁f : b₁ ≫ f = h) (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a) :
    b₁ = b₂ :=
  have : IsClosedImmersion i := hi.1
  FormallyUnramified.hom_ext i ⟨2, hi.2⟩ f (by rw [hb₁a, hb₂a]) (by rw [hb₁f, hb₂f])

/-- **A smooth formally unramified morphism of schemes is formally smooth**, with no affineness
hypothesis on the morphism. Lifts exist locally on the thickening by
`Stacks.Smooth.exists_isAffineOpen_lift`, they agree on overlaps by
`Stacks.Smooth.lift_unique` applied to the restricted thickening, and they therefore glue by
`Stacks.Smooth.exists_lift_of_isOpenCover`.

This is the case of the missing direction of [Stacks Project, Tag 02H6] in which the correction
step of the Stacks proof is vacuous, uniqueness of local lifts replacing the vanishing of the
first cohomology of the sheaf of derivations. -/
theorem formallySmoothScheme_of_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [FormallyUnramified f] : FormallySmoothScheme f := by
  intro T T' _ _ i hi a h hcomm
  have hci : IsClosedImmersion i := hi.1
  choose V' hV'affine htV' b hbf hba using exists_isAffineOpen_lift f hi a h hcomm
  have hcover : TopologicalSpace.IsOpenCover V' :=
    top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, htV' x⟩
  refine exists_lift_of_isOpenCover f i a h V' hcover b hbf hba fun j k => ?_
  have hres : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
      (i ∣_ (V' j ⊓ V' k)) ≫ T'.homOfLE e ≫ b l = (i ⁻¹ᵁ (V' j ⊓ V' k)).ι ≫ a := by
    intro l e
    rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba l, ← Category.assoc,
      Scheme.homOfLE_ι]
  have hresf : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
      (T'.homOfLE e ≫ b l) ≫ f = (V' j ⊓ V' k).ι ≫ h := by
    intro l e
    rw [Category.assoc, hbf l, ← Category.assoc, Scheme.homOfLE_ι]
  have hthick := isFirstOrderThickening_morphismRestrict hi (V' j ⊓ V' k)
  have hci' : IsClosedImmersion (i ∣_ (V' j ⊓ V' k)) := hthick.1
  exact FormallyUnramified.hom_ext (i ∣_ (V' j ⊓ V' k)) ⟨2, hthick.2⟩ f
    (by rw [hres j inf_le_left, hres k inf_le_right])
    (by rw [hresf j inf_le_left, hresf k inf_le_right])

/-- Formal smoothness is stable under composition: lift along the second morphism first, then
along the first. -/
theorem FormallySmoothScheme.comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : FormallySmoothScheme f) (hg : FormallySmoothScheme g) :
    FormallySmoothScheme (f ≫ g) := by
  intro T T' hT hT' i hi a h hcomm
  obtain ⟨c, hc₁, hc₂⟩ := hg hT hT' i hi (a ≫ f) h (by rwa [Category.assoc])
  obtain ⟨b, hb₁, hb₂⟩ := hf hT hT' i hi a c hc₂.symm
  exact ⟨b, by rw [← Category.assoc, hb₁, hc₁], hb₂⟩

/-- **An étale morphism of schemes is formally smooth**, with no affineness hypothesis: an étale
morphism is smooth and formally unramified. -/
theorem formallySmoothScheme_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    FormallySmoothScheme f :=
  formallySmoothScheme_of_formallyUnramified f

/-- An open immersion of schemes is formally smooth. -/
theorem formallySmoothScheme_of_isOpenImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsOpenImmersion f] : FormallySmoothScheme f :=
  formallySmoothScheme_of_etale f

end Stacks.Smooth

end
