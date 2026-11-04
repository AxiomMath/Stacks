module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Gluing
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian0200

/-!
# Chow's lemma over a Noetherian base, reduced to the affine case

**Stacks Tag 0200** says that a separated finite-type morphism `f : X ⟶ S` over a Noetherian
base admits a proper surjective modification `π : X' ⟶ X` with `X'` immersed in a projective
space over `S`, compatibly with the maps to `S`, and with `π` an isomorphism over a dense open
subscheme of `X`.

This file proves that statement from one named input,
`Stacks.AlgebraicGeometry.ChowNoetherianBase.HasAffineProjectiveImmersion S`: *every affine
scheme locally of finite type over `S` admits an immersion into some projective space over `S`,
over `S`.* Nothing else is assumed.

## Main definitions

* `Stacks.AlgebraicGeometry.ChowNoetherianBase.HasAffineProjectiveImmersion`: the single input.
* `Stacks.AlgebraicGeometry.ChowNoetherianBase.ChowDiagram`: the diagram of Chow's lemma,
  including the dense open over which its proper map is an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ChowNoetherianBase.exists_chowDiagram`: Chow's lemma over a
  Noetherian base, from the input above.

## Implementation notes

The input is strictly weaker than Stacks Tag 01VS, which the source's own proof invokes: 01VS
produces the immersion for all sufficiently high powers of an arbitrary ample invertible sheaf,
while only the affine case with `L = 𝒪_X` is used, with no twist identification and no degree
bound. Isolating it that way also removes the Tag 01QE step (ampleness of the structure sheaf of
a quasi-affine scheme) from the chain.

Projective space over `S` is `AlgebraicGeometry.projectiveSpaceOver`, which is definitionally
`AlgebraicGeometry.ProjectiveSpace`; properness of its structure morphism is taken from
`AlgebraicGeometry.ProjectiveSpace.instIsProperOver` along that identification. The two
`CanonicallyOver` instances are distinct declarations, so instance search does not cross between
the spellings and `AlgebraicGeometry.isProper_projectiveSpaceOver` performs the transport once.

**No Stacks attribute for 0200 is attached here, and it is withheld deliberately.** Tag 0200 has
one labelled assertion, and the statement proved here carries `HasAffineProjectiveImmersion S`,
a hypothesis the tag does not grant. Under the covering-set rule there is therefore no covering
set, and the tag is earned the moment that hypothesis is discharged — at which point it belongs
on `Stacks.AlgebraicGeometry.ChowNoetherianBase.nonempty_chowDiagram`, whose conclusion is the
tag's assertion verbatim.

The inputs of the source's own argument resolve as follows. The Segre embedding is
`Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding` (Tag 01WD, proved and tagged,
hypothesising nothing beyond the base scheme). The common affine neighbourhood of a point and
finitely many generic points is
`AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents` (Tag 01ZX,
proved and tagged). Scheme-theoretic dominance of the map to the scheme-theoretic image is
`AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_toImage`, which makes the source's
detour through Tags 01RB and 01RG unnecessary: those two establish scheme-theoretic *density* of
the image open only to deduce that dominance back again. Tag 01QE (ampleness of the structure
sheaf of a quasi-affine scheme) drops out with the ampleness formulation of the input.

## References

* [EGA II, Theorem 5.6.1(a)]
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Stacks.AlgebraicGeometry.ChowNoetherianBase

universe u

/-- **The single input of this file.** Every affine scheme locally of finite type over `S`
admits an immersion into some projective space over `S`, lying over `S`.

This is the affine case of Stacks Tag 01VS with `L = 𝒪_X`, with the twist identification and the
degree bound dropped. -/
def HasAffineProjectiveImmersion (S : Scheme.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ S), IsAffine Y → LocallyOfFiniteType g →
    ∃ (n : ℕ) (i : Y ⟶ projectiveSpaceOver n S),
      IsImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = g

/-- A Chow modification of `X` over `S`: a proper surjective map from a scheme immersed in
projective space over `S`, which is an isomorphism over a dense open subscheme of `X`. -/
structure ChowDiagram {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the ambient projective space. -/
  n : ℕ
  /-- The modified scheme. -/
  scheme : Scheme.{u}
  /-- The modification. -/
  toX : scheme ⟶ X
  /-- The immersion into projective space over `S`. -/
  toProjectiveSpace : scheme ⟶ projectiveSpaceOver n S
  /-- The dense open over which the modification is an isomorphism. -/
  denseOpen : X.Opens
  /-- The modification is proper. -/
  isProper : IsProper toX
  /-- The modification is surjective. -/
  surjective : Surjective toX
  /-- The map to projective space is an immersion. -/
  isImmersion : IsImmersion toProjectiveSpace
  /-- The triangle over `S` commutes. -/
  commutes : toX ≫ f = toProjectiveSpace ≫ (projectiveSpaceOver n S ↘ S)
  /-- The distinguished open is dense. -/
  dense : Dense (denseOpen : Set X)
  /-- The modification restricts to an isomorphism over the distinguished open. -/
  isIso_restrict : IsIso (toX ∣_ denseOpen)

/-- Package a proper surjective modification and its dense open isomorphism as a
`Stacks.AlgebraicGeometry.ChowNoetherianBase.ChowDiagram`. -/
theorem nonempty_chowDiagram_of_data {X S Y : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (π : Y ⟶ X)
    (i : Y ⟶ projectiveSpaceOver n S) (U : X.Opens)
    (hproper : IsProper π) (hsurjective : Surjective π) (himmersion : IsImmersion i)
    (hcomm : π ≫ f = i ≫ (projectiveSpaceOver n S ↘ S))
    (hdense : Dense (U : Set X)) (hiso : IsIso (π ∣_ U)) :
    Nonempty (ChowDiagram f) :=
  ⟨{ n := n, scheme := Y, toX := π, toProjectiveSpace := i, denseOpen := U
     isProper := hproper, surjective := hsurjective, isImmersion := himmersion
     commutes := hcomm, dense := hdense, isIso_restrict := hiso }⟩

/-- An already immersed finite-type scheme is its own Chow modification. -/
theorem nonempty_chowDiagram_of_isImmersion {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (i : X ⟶ projectiveSpaceOver n S) (hi : IsImmersion i)
    (hcomm : 𝟙 X ≫ f = i ≫ (projectiveSpaceOver n S ↘ S)) :
    Nonempty (ChowDiagram f) := by
  apply nonempty_chowDiagram_of_data f n (𝟙 X) i ⊤ inferInstance ⟨fun x => ⟨x, rfl⟩⟩ hi hcomm
    (by simp)
  infer_instance

/-- Properness promotes a map whose image contains a dense open to a surjection. -/
theorem surjective_of_proper_of_dense_open {X Y : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (U : X.Opens) (s : U.toScheme ⟶ Y) (hπ : s ≫ π = U.ι) (hU : Dense (U : Set X)) :
    Surjective π := by
  have hdense : IsDominant (s ≫ π) := by
    rw [hπ]
    exact Opens.isDominant_ι hU
  have : IsDominant π := IsDominant.of_comp s π
  exact inferInstance

/-- Closed immersions are stable under composition.

Supplied as a term: `MorphismProperty.IsMultiplicative @IsClosedImmersion` is an instance in
Mathlib but instance search does not derive `IsStableUnderComposition` from it outside that
file, and the resulting failure is reported against the derived class. -/
theorem isStableUnderComposition_isClosedImmersion :
    MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- The Segre step. A fibre product `ℙⁿ_S ×_S A`, for `A` closed-immersed in `ℙᵐ_S` over `S`, is
itself closed-immersed in a single projective space over `S`, over `S`.

Stated with every ingredient a variable so that the identification is an instantiation rather
than a unification against a composite. -/
theorem exists_closedImmersion_pullback_of_closedImmersion {S A : Scheme.{u}} (n m : ℕ)
    (q : A ⟶ S) (i : A ⟶ projectiveSpaceOver m S) (hi : IsClosedImmersion i)
    (hcomm : i ≫ (projectiveSpaceOver m S ↘ S) = q) :
    ∃ (N : ℕ) (g : pullback (projectiveSpaceOver n S ↘ S) q ⟶ projectiveSpaceOver N S),
      IsClosedImmersion g ∧ g ≫ (projectiveSpaceOver N S ↘ S) =
        pullback.fst (projectiveSpaceOver n S ↘ S) q ≫ (projectiveSpaceOver n S ↘ S) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    isStableUnderComposition_isClosedImmersion
  obtain ⟨e, he, hbase⟩ := SegreProdIso.exists_segreEmbedding n m S
  refine ⟨n * m + n + m, pullback.map (projectiveSpaceOver n S ↘ S) q
    (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) (𝟙 _) i (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hcomm.symm) ≫ e,
    MorphismProperty.comp_mem @IsClosedImmersion _ _
      (MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance hi
        (Category.id_comp _).symm hcomm.symm) he, ?_⟩
  rw [Category.assoc, hbase, pullback.lift_fst_assoc, Category.comp_id]

/-- A chart into `AlgebraicGeometry.projectiveSpaceOver` is an
`AlgebraicGeometry.ProjectiveFactor`, whose field is spelled with
`AlgebraicGeometry.ProjectiveSpace`: the two are the same scheme, and their structure morphisms
are the same morphism, so the data transfers unchanged. -/
noncomputable def projectiveFactorOfOver {X S : Scheme.{u}} {f : X ⟶ S} (n : ℕ)
    (i : X ⟶ projectiveSpaceOver n S) (hi : IsImmersion i)
    (h : i ≫ (projectiveSpaceOver n S ↘ S) = f) : ProjectiveFactor f where
  n := n
  map := i
  isImmersion := hi
  commutes := h

/-- A finite relative projective product embeds as a closed subscheme of a single relative
projective space, by iterating the Segre embedding. -/
theorem relativeProjectiveProduct_isProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (l : List (ProjectiveFactor f)) (hne : l ≠ []) :
    ∃ n : ℕ, ∃ i : relativeProjectiveProduct l ⟶ projectiveSpaceOver n S,
      IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver n S ↘ S) = relativeProjectiveProductBase l := by
  induction l with
  | nil => simp at hne
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact ⟨a.n, 𝟙 (projectiveSpaceOver a.n S), (inferInstance : IsClosedImmersion (𝟙 _)),
            Category.id_comp _⟩
      | cons b tail =>
          obtain ⟨m, i, hi, hcomm⟩ := ih (by simp)
          exact exists_closedImmersion_pullback_of_closedImmersion a.n m
            (relativeProjectiveProductBase (f := f) (b :: tail)) i hi hcomm

/-- Each factor of a relative projective product is the target of a projection from the product,
compatibly with the base and with the diagonal map. -/
theorem exists_relativeProjectiveProductProjection {X S : Scheme.{u}} (f : X ⟶ S)
    (l : List (ProjectiveFactor f)) (b : ProjectiveFactor f) (hb : b ∈ l) :
    ∃ r : relativeProjectiveProduct l ⟶ projectiveSpaceOver b.n S,
      r ≫ (projectiveSpaceOver b.n S ↘ S) = relativeProjectiveProductBase l ∧
      (relativeProjectiveProductMap f l).1 ≫ r = b.map := by
  induction l with
  | nil => simp at hb
  | cons a rest ih =>
      cases rest with
      | nil =>
          have : b = a := by simpa using hb
          subst b
          exact ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
      | cons c tail =>
          rcases List.mem_cons.mp hb with h | h
          · subst b
            exact ⟨pullback.fst (projectiveSpaceOver a.n S ↘ S)
              (relativeProjectiveProductBase (f := f) (c :: tail)), rfl,
              pullback.lift_fst _ _ _⟩
          · obtain ⟨r, hr, hm⟩ := ih h
            refine ⟨pullback.snd (projectiveSpaceOver a.n S ↘ S)
              (relativeProjectiveProductBase (f := f) (c :: tail)) ≫ r, ?_, ?_⟩
            · refine (Category.assoc _ _ _).trans ?_
              rw [hr]
              exact pullback.condition.symm
            · exact (pullback.lift_snd_assoc _ _ _ _).trans hm

/-- The scheme-theoretic image of the common open has a proper chart over each member of the
cover. -/
theorem exists_chart_of_image {X S P : Scheme.{u}} (f : X ⟶ S) (q : P ⟶ S) [IsProper q]
    (U V : X.Opens) (hUV : U ≤ V) (a : U.toScheme ⟶ P) [IsImmersion a] [QuasiCompact a]
    (n : ℕ) (j : V.toScheme ⟶ projectiveSpaceOver n S) [IsImmersion j] [QuasiCompact j]
    (hj : j ≫ (projectiveSpaceOver n S ↘ S) = V.ι ≫ f) (r : P ⟶ projectiveSpaceOver n S)
    (hr : r ≫ (projectiveSpaceOver n S ↘ S) = q) (har : a ≫ r = X.homOfLE hUV ≫ j) :
    ∃ (W : Scheme.{u}) (e : W ⟶ a.image) (p : W ⟶ V.toScheme) (s : U.toScheme ⟶ W),
      IsOpenImmersion e ∧ IsProper p ∧ s ≫ e = a.toImage ∧
      s ≫ p = X.homOfLE hUV ∧ e ≫ a.imageι ≫ q = p ≫ V.ι ≫ f := by
  have hk : j.imageι.ker ≤ (a.imageι ≫ r).ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    have H : (a.toImage ≫ (a.imageι ≫ r)).ker = (a.imageι ≫ r).ker := by
      rw [Scheme.Hom.ker_comp, a.toImage.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← H, ← Category.assoc, a.toImage_imageι, har]
    exact Scheme.Hom.le_ker_comp _ _
  let r' : a.image ⟶ j.image := IsClosedImmersion.lift j.imageι (a.imageι ≫ r) hk
  have hr' : r' ≫ j.imageι = a.imageι ≫ r := IsClosedImmersion.lift_fac _ _ _
  have : IsProper (projectiveSpaceOver n S ↘ S) :=
    AlgebraicGeometry.isProper_projectiveSpaceOver n S
  have hr'base : r' ≫ (j.imageι ≫ (projectiveSpaceOver n S ↘ S)) = a.imageι ≫ q := by
    rw [← Category.assoc, hr', Category.assoc, hr]
  have : IsProper (r' ≫ (j.imageι ≫ (projectiveSpaceOver n S ↘ S))) := by
    rw [hr'base]; infer_instance
  have : IsProper r' := IsProper.of_comp r' (j.imageι ≫ (projectiveSpaceOver n S ↘ S))
  have ha : a.toImage ≫ r' = X.homOfLE hUV ≫ j.toImage := by
    apply (cancel_mono j.imageι).mp
    rw [Category.assoc, hr', ← Category.assoc, a.toImage_imageι, Category.assoc,
      j.toImage_imageι, har]
  refine ⟨pullback r' j.toImage, pullback.fst _ _, pullback.snd _ _,
    pullback.lift a.toImage (X.homOfLE hUV) ha, inferInstance, inferInstance,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  rw [← hr'base, pullback.condition_assoc]
  simp only [Scheme.Hom.toImage_imageι_assoc]
  rw [hj]

/-- **Chow's lemma over a Noetherian base, Stacks Tag 0200**, from the affine case.

A separated finite-type morphism to a Noetherian scheme has a proper surjective modification
immersed in a projective space over the base, and the modification is an isomorphism over a
dense open subscheme. -/
theorem nonempty_chowDiagram {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hinput : HasAffineProjectiveImmersion S) :
    Nonempty (ChowDiagram f) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  obtain ⟨F, U, hAffine, hcover, hSubset, hdense⟩ :=
    exists_finite_dense_affine_open_cover (X := X)
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  by_cases hF : F.Nonempty
  · let I := {V : X.Opens // V ∈ F}
    have : Nonempty I := by
      obtain ⟨V, hV⟩ := hF
      exact ⟨⟨V, hV⟩⟩
    have : ∀ V : I, NoetherianSpace V.val.toScheme :=
      fun V => V.val.ι.isOpenEmbedding.isInducing.noetherianSpace
    have hcharts (V : I) : ∃ (n : ℕ) (i : V.val.toScheme ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = V.val.ι ≫ f := by
      have : IsAffine V.val.toScheme := hAffine V.val V.property
      exact hinput V.val.toScheme (V.val.ι ≫ f) inferInstance inferInstance
    choose n j hj hcomm using hcharts
    have : ∀ V, IsImmersion (j V) := hj
    let A (V : I) : ProjectiveFactor (U.ι ≫ f) :=
      projectiveFactorOfOver (n V) (X.homOfLE (hSubset V.val V.property) ≫ j V) inferInstance
        (by rw [Category.assoc, hcomm, Scheme.homOfLE_ι_assoc])
    let l := F.attach.toList.map A
    have hmem (V : I) : A V ∈ l := List.mem_map.mpr
      ⟨V, Finset.mem_toList.mpr (F.mem_attach V), rfl⟩
    have hl : l ≠ [] := by
      intro h
      have := hmem (Classical.choice inferInstance)
      simp [h] at this
    have hamap : IsImmersion (relativeProjectiveProductMap (U.ι ≫ f) l).1 :=
      isImmersion_relativeProjectiveProductMap _ l hl
    obtain ⟨N, e, he, heq⟩ := relativeProjectiveProduct_isProjective l hl
    have : IsClosedImmersion e := he
    have : IsProper (projectiveSpaceOver N S ↘ S) :=
      AlgebraicGeometry.isProper_projectiveSpaceOver N S
    have hq : IsProper (relativeProjectiveProductBase (f := U.ι ≫ f) l) := by
      rw [← heq]
      infer_instance
    have hr (V : I) := exists_relativeProjectiveProductProjection (U.ι ≫ f) l (A V) (hmem V)
    choose r hrbase hramap using hr
    have hlocal (V : I) := ChowNoetherianBase.exists_chart_of_image f
      (relativeProjectiveProductBase (f := U.ι ≫ f) l) U V.val
      (hSubset V.val V.property) (relativeProjectiveProductMap (U.ι ≫ f) l).1
      (n V) (j V) (hcomm V) (r V) (hrbase V) (hramap V)
    choose W k p s hk hp hsk hsp hkbase using hlocal
    have : ∀ V, IsOpenImmersion (k V) := hk
    have : ∀ V, IsProper (p V) := hp
    obtain ⟨Y, i, π, t, hi, hπ, hiq, hti, htπ, hiso⟩ :=
      exists_modification_of_dense_charts f
        ((relativeProjectiveProductMap (U.ι ≫ f) l).1.imageι ≫
          relativeProjectiveProductBase (f := U.ι ≫ f) l) U
        (relativeProjectiveProductMap (U.ι ≫ f) l).1.toImage
        (fun V : I => V.val) (fun x => by
          obtain ⟨V, hV, hxV⟩ := hcover x
          exact ⟨⟨V, hV⟩, hxV⟩)
        (fun V => hSubset V.val V.property) W k p s hsk hsp hkbase
    have : IsOpenImmersion i := hi
    have : IsProper π := hπ
    refine nonempty_chowDiagram_of_data f N π
      (i ≫ (relativeProjectiveProductMap (U.ι ≫ f) l).1.imageι ≫ e) U hπ
      (surjective_of_proper_of_dense_open π U t htπ hdense) inferInstance ?_ hdense hiso
    rw [← hiq, Category.assoc, Category.assoc, heq]
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨V, hV, -⟩ := hcover x
      exact hF ⟨V, hV⟩⟩
    have : IsAffine X := inferInstance
    obtain ⟨n, i, hi, hcomm⟩ := hinput X f inferInstance inferInstance
    exact nonempty_chowDiagram_of_isImmersion f n i hi (by simpa using hcomm.symm)

/-- **Chow's lemma over a Noetherian base in the form the rest of the development consumes.**
`AlgebraicGeometry.HasChowModification` is the conclusion of Stacks Tag 0202 as stated in
`StacksFrontier/AlgebraicGeometry/Limits/ChowLemma.lean`; it forgets the dense open. Over a
Noetherian base it follows from the affine input alone.

Composing with `AlgebraicGeometry.HasChowModification.of_isClosedImmersion` is the opening
reduction of Tag 0202. -/
theorem hasChowModification {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hinput : HasAffineProjectiveImmersion S) :
    HasChowModification f := by
  obtain ⟨m⟩ := nonempty_chowDiagram f hinput
  exact ⟨m.n, m.scheme, m.toX, m.toProjectiveSpace, m.isProper, m.surjective, m.isImmersion,
    m.commutes⟩

end Stacks.AlgebraicGeometry.ChowNoetherianBase

end
