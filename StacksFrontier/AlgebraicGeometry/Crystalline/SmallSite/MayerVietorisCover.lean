module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.Restriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# Mayer--Vietoris for an open covering on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` and an open covering `X = X' ∪ X''`, with
`X''' = X' ∩ X''`.  Each object `(U, T, δ)` of the small crystalline site `Cris(X/S)` meets the
three opens: the immersion `U ↪ T` is a surjective closed immersion, hence a homeomorphism, so an
open `V` of `X` cuts out a unique open `V_T` of the ambient scheme `T` with `V_T ∩ U = U ∩ f⁻¹(V)`,
and `(U, T, δ)` restricts to `(U ∩ V, V_T, δ|_{V_T})`, again an object of `Cris(X/S)`.

The square of restrictions of `(U, T, δ)` to `X'''`, `X'`, `X''` and `(U, T, δ)` itself is then a
*Mayer--Vietoris square* of the site: it is cartesian, its two lower edges are monomorphisms, and
they generate a covering sieve.  Consequently the sections of any sheaf on `Cris(X/S)` over the
four corners form a cartesian square; for a sheaf of abelian groups that square is the exactness
of `0 ⟶ F(U, T, δ) ⟶ F' ⊕ F'' ⟶ F'''`, the Mayer--Vietoris sequence of the covering.

## What of [Stacks, Tag 07ML] is formalized

The tag asserts, in the situation of [Stacks, Tag 07MJ], a distinguished triangle
`Rf_{cris,*}F ⟶ Rf'_{cris,*}F' ⊕ Rf''_{cris,*}F'' ⟶ Rf'''_{cris,*}F''' ⟶ Rf_{cris,*}F[1]`
in `D(𝒪_{X'/S'})`, and says of it only that it "is a formal consequence of the fact that the
subcategories `Cris(X'/S)`, `Cris(X''/S)`, `Cris(X'''/S)` correspond to open subobjects of the
final sheaf on `Cris(X/S)` and that the last is the intersection of the first two".

It is that geometric input which is formalized here, in the form the standard Mayer--Vietoris
idiom takes on a site: `CrystallineThickening.isPullback_sections_openCoverSquare`.  For an
abelian sheaf the square is upgraded to a *short exact* sequence, at an injective sheaf, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisShortExact.lean`
(`CrystallineThickening.openCoverShortComplex_shortExact`), which is the form a derived functor
consumes; that is a separate module because it reaches the generic site lemmas of the étale
cohomology tree, which this file declines to import.

The triangle is formalized at a *fixed object* of the site, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisTriangle.lean`: the per-object
sequences above are assembled there into a short exact sequence of *functors* on
`Ab(Cris(X/S))`, short exact at every injective, and fed to the derived machinery
(`...CrystallineThickening.openCoverTriangle_distinguished`, and the long exact sequence
`...longExact_openCoverFunctorComplex`).  The comparison the remark takes for granted,
identifying `Cris(X'/S)` with the localization of `Cris(X/S)` at the open subobject `X'` of the
final sheaf — clause (d) of [Stacks, Tag 07KL] — is also formalized, as
`Crystalline.GlobalCrystallineSituation.openSubspaceSliceEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectLocalization.lean`.  What is
**not** formalized is the remark's own
statement, whose terms are the derived *global* sections of the four crystalline sites: the
functors of the triangle above are sections at a fixed object, and `Cris(X/S)` has no terminal
object for the two to coincide, so the sequence would have to be redone for global sections.

Three further ingredients are available, and no claim to the contrary should be read into the
paragraph above.  The abelian derived direct image `Rf_{cris, *}` is formalized, as
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedCrisDirectImageFunctor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisDirectImage.lean`, together with
`...preservesInjectiveObjects_crisDirectImage`; the module-valued `R^i f_{cris, *}` is formalized as
`...higherCrisModuleDirectImage` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisModuleDirectImage.lean`; and the
situation
`X'/S` attached to an open `X'` of `X` is formalized as
`Crystalline.GlobalCrystallineSituation.restrict` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/SituationRestrict.lean`.  So the triangle does
not want a derived pushforward or a restricted situation; it wants the localization.

## Main definitions

* `CrystallineThickening.ambientOpen` — the open of the ambient scheme of an object of
  `Cris(X/S)` cut out by an open of `X`.
* `CrystallineThickening.openCoverSquare` — the Mayer--Vietoris square of a pair of opens of `X`
  at an object of `Cris(X/S)`.

## Main results

* `CrystallineThickening.isPullback_openCoverSquare` — the square is cartesian: the restriction to
  `X'''` is the intersection of the restrictions to `X'` and `X''`.
* `CrystallineThickening.ofTwoArrows_openCoverSquare_mem_smallTopology` — the two restrictions
  generate a covering sieve when `X = X' ∪ X''`.
* `CrystallineThickening.isPullback_sections_openCoverSquare` — **[Stacks, Tag 07ML]**, the
  geometric input of the remark: the sections of a sheaf on `Cris(X/S)` over the square form a
  cartesian square.

## Implementation notes

Mathlib bundles the three conditions as `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`,
and that bundling is *not available here*: it is stated for a site `C : Type u` with
`Category.{v} C` under `[HasWeakSheafify J (Type v)]`, whereas the small crystalline site has its
objects one universe above its morphisms — `CrystallineThickening S : Type (u + 1)` with
`Category.{u}` — so the sheafification it asks for is of `Type u`-valued presheaves, which does
not exist; the crystalline topos is `Sheaf (smallTopology S) (Type (u + 1))`.  The three
conditions are therefore recorded separately, in exactly the shape
`GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback` consumes, so that the bundling becomes
a one-line construction if Mathlib's universe assumption is ever relaxed.

For the same reason `isPullback_sections_openCoverSquare` does not go through
`Stacks.EtaleCohomology.RelativeMayerVietoris.sheaf_pullback_of_cover`, which is the same
assertion for an arbitrary site and an `AddCommGrpCat`-valued sheaf: reaching it means importing
the étale cohomology tree into the crystalline tree. The statement proved here is instead general
in the value category of the sheaf, which is what `Presheaf.IsSheaf.amalgamateOfArrows` supports.

The universal property used for the cartesian square is
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.exists_comp_restrictOpenHom_eq`: a morphism into an object whose ambient scheme maps into an
open factors through the restriction to that open, uniquely because the structure morphism of a
restriction is a monomorphism.  That its ambient scheme does map into the open is the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.comp_restrictOpenHom_targetHom_base_mem`, which
applies verbatim: a morphism of `Cris(X/S)` is a morphism of `CRIS(X/S)` in its field `hom`, and
restriction to an open is the same construction on both sites.  The covering condition is
`restrictCoverage`: a family of
restrictions of an object to an open cover of its ambient scheme covers in `Cris(X/S)`, and the
pair indexed by `WalkingPair` is such a family after transport to `Type (u + 1)`.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w v u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The open of an ambient scheme cut out by an open of `X` -/

/-- **The open of the ambient scheme `T` of an object `(U, T, δ)` of `Cris(X/S)` cut out by an open
`V` of `X`**: the unique open of `T` whose intersection with `U` is the preimage of `V` in `U`.  It
exists because the immersion `U ↪ T` is a surjective closed immersion, hence a homeomorphism. -/
def ambientOpen (A : CrystallineThickening S) (V : S.X.Opens) :
    A.obj.thickening.target.scheme.Opens :=
  Stacks.Thickenings.IsThickening.opensCongr A.obj.thickening.isThickening (A.obj.toX ⁻¹ᵁ V)

/-- **The open cut out by an open `V` of `X` has preimage in `U` the preimage of `V`.**  This is
what characterizes it. -/
theorem immersion_preimage_ambientOpen (A : CrystallineThickening S) (V : S.X.Opens) :
    A.obj.thickening.immersion ⁻¹ᵁ ambientOpen A V = A.obj.toX ⁻¹ᵁ V :=
  Stacks.Thickenings.IsThickening.preimage_opensCongr _ _

/-- **Cutting out an open of the ambient scheme is monotone in the open of `X`.** -/
theorem ambientOpen_le_ambientOpen (A : CrystallineThickening S) {V V' : S.X.Opens} (h : V ≤ V') :
    ambientOpen A V ≤ ambientOpen A V' :=
  (Stacks.Thickenings.IsThickening.opensCongr _).monotone fun _ hx ↦ h hx

/-- **Cutting out an open of the ambient scheme commutes with intersections.** -/
theorem ambientOpen_inf (A : CrystallineThickening S) (V V' : S.X.Opens) :
    ambientOpen A (V ⊓ V') = ambientOpen A V ⊓ ambientOpen A V' := by
  unfold ambientOpen
  rw [← OrderIso.map_inf]
  congr 1

/-- **Cutting out an open of the ambient scheme commutes with unions.** -/
theorem ambientOpen_sup (A : CrystallineThickening S) (V V' : S.X.Opens) :
    ambientOpen A (V ⊔ V') = ambientOpen A V ⊔ ambientOpen A V' := by
  unfold ambientOpen
  rw [← OrderIso.map_sup]
  congr 1

/-- **The whole of `X` cuts out the whole ambient scheme.** -/
theorem ambientOpen_top (A : CrystallineThickening S) : ambientOpen A ⊤ = ⊤ := by
  unfold ambientOpen
  rw [show (A.obj.toX ⁻¹ᵁ (⊤ : S.X.Opens)) = ⊤ from TopologicalSpace.Opens.ext (by simp)]
  exact OrderIso.map_top _

/-! ### The Mayer--Vietoris square of a pair of opens -/

/-- **The restriction of an object of `Cris(X/S)` to an intersection of two opens of its ambient
scheme is the fibre product of the two restrictions.**  A morphism into the object whose ambient
scheme maps into both opens maps into their intersection, hence factors through the restriction to
it, uniquely because that restriction's structure morphism is a monomorphism. -/
theorem isPullback_restrictOpenHom (A : CrystallineThickening S)
    {W₀ W₁ W₂ : A.obj.thickening.target.scheme.Opens} (hW : W₀ = W₁ ⊓ W₂) (h₁ : W₀ ≤ W₁)
    (h₂ : W₀ ≤ W₂) :
    IsPullback (restrictOpenLE A h₁) (restrictOpenLE A h₂)
      (A.restrictOpenHom W₁) (A.restrictOpenHom W₂) := by
  subst hW
  have hfac : restrictOpenLE A h₁ ≫ A.restrictOpenHom W₁ =
      restrictOpenLE A h₂ ≫ A.restrictOpenHom W₂ :=
    (restrictOpenLE_restrictOpenHom A _).trans (restrictOpenLE_restrictOpenHom A _).symm
  have key : ∀ s : PullbackCone (A.restrictOpenHom W₁) (A.restrictOpenHom W₂),
      ∃ p : s.pt ⟶ A.restrictOpen (W₁ ⊓ W₂),
        p ≫ A.restrictOpenHom (W₁ ⊓ W₂) = s.fst ≫ A.restrictOpenHom W₁ := fun s ↦ by
    refine exists_comp_restrictOpenHom_eq _ _ fun x ↦
      ⟨Thickening.comp_restrictOpenHom_targetHom_base_mem W₁ s.fst.hom x, ?_⟩
    rw [s.condition]
    exact Thickening.comp_restrictOpenHom_targetHom_base_mem W₂ s.snd.hom x
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hfac (fun s ↦ (key s).choose)
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ _ ↦ ?_))
  · refine (cancel_mono (A.restrictOpenHom W₁)).1 ?_
    rw [Category.assoc, restrictOpenLE_restrictOpenHom, (key s).choose_spec]
  · refine (cancel_mono (A.restrictOpenHom W₂)).1 ?_
    rw [Category.assoc, restrictOpenLE_restrictOpenHom, (key s).choose_spec, s.condition]
  · refine (cancel_mono (A.restrictOpenHom (W₁ ⊓ W₂))).1 ?_
    rw [(key s).choose_spec, ← restrictOpenLE_restrictOpenHom A h₁, ← Category.assoc, hm₁]

/-- **The restrictions of an object of `Cris(X/S)` to two opens covering its ambient scheme
generate a covering sieve.**  The pair is a family of restrictions to an open cover of the ambient
scheme, and such families cover, `restrictCoverage`. -/
theorem ofTwoArrows_restrictOpenHom_mem_smallTopology (A : CrystallineThickening S)
    {W₁ W₂ : A.obj.thickening.target.scheme.Opens} (h : W₁ ⊔ W₂ = ⊤) :
    Sieve.ofTwoArrows (A.restrictOpenHom W₁) (A.restrictOpenHom W₂) ∈ smallTopology S A := by
  let V : ULift.{u + 1} WalkingPair → A.obj.thickening.target.scheme.Opens :=
    fun i ↦ WalkingPair.casesOn i.down W₁ W₂
  have hV : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i := fun x ↦ by
    have hx : x ∈ (W₁ ⊔ W₂ : A.obj.thickening.target.scheme.Opens) := h ▸ trivial
    rcases hx with hx | hx
    · exact ⟨⟨WalkingPair.left⟩, hx⟩
    · exact ⟨⟨WalkingPair.right⟩, hx⟩
  have heq : Sieve.ofTwoArrows (A.restrictOpenHom W₁) (A.restrictOpenHom W₂) =
      Sieve.generate (A.restrictOpenCover V).presieve₀ := by
    refine le_antisymm ?_ ?_
    · rw [Sieve.generate_le_iff]
      rintro Z k ⟨(_ | _)⟩
      · exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (ULift.up WalkingPair.left))
      · exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (ULift.up WalkingPair.right))
    · rw [Sieve.generate_le_iff]
      rintro Z k ⟨⟨(_ | _)⟩⟩
      · exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk WalkingPair.left)
      · exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk WalkingPair.right)
  rw [heq]
  exact generate_mem_smallTopology_of_mem_restrictCoverage S
    (A := A) (R := (A.restrictOpenCover V).presieve₀) ⟨_, V, hV, rfl⟩

/-- **The Mayer--Vietoris square of a pair of opens `X'`, `X''` of `X` at an object `(U, T, δ)` of
`Cris(X/S)`**: the restrictions of `(U, T, δ)` to the opens of `T` cut out by `X' ∩ X''`, by `X'`
and by `X''`, over `(U, T, δ)` itself. -/
def openCoverSquare (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    Square (CrystallineThickening S) where
  f₁₂ := restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
  f₁₃ := restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_right : V₁ ⊓ V₂ ≤ V₂))
  f₂₄ := A.restrictOpenHom (ambientOpen A V₁)
  f₃₄ := A.restrictOpenHom (ambientOpen A V₂)
  fac := (restrictOpenLE_restrictOpenHom A _).trans (restrictOpenLE_restrictOpenHom A _).symm

/-- **The Mayer--Vietoris square of a pair of opens of `X` is cartesian.**  The restriction to
`X' ∩ X''` is the fibre product of the restrictions to `X'` and to `X''`: cutting out an open of
the ambient scheme commutes with intersections. -/
theorem isPullback_openCoverSquare (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    (openCoverSquare A V₁ V₂).IsPullback :=
  isPullback_restrictOpenHom A (ambientOpen_inf A V₁ V₂) _ _

/-- The right edge of the Mayer--Vietoris square is a monomorphism. -/
instance mono_openCoverSquare_f₂₄ (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    Mono (openCoverSquare A V₁ V₂).f₂₄ :=
  inferInstanceAs (Mono (A.restrictOpenHom (ambientOpen A V₁)))

/-- The lower edge of the Mayer--Vietoris square is a monomorphism. -/
instance mono_openCoverSquare_f₃₄ (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    Mono (openCoverSquare A V₁ V₂).f₃₄ :=
  inferInstanceAs (Mono (A.restrictOpenHom (ambientOpen A V₂)))

/-- **The two lower edges of the Mayer--Vietoris square of an open covering `X = X' ∪ X''`
generate a covering sieve.** -/
theorem ofTwoArrows_openCoverSquare_mem_smallTopology (A : CrystallineThickening S)
    {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤) :
    Sieve.ofTwoArrows (openCoverSquare A V₁ V₂).f₂₄ (openCoverSquare A V₁ V₂).f₃₄ ∈
      smallTopology S (openCoverSquare A V₁ V₂).X₄ :=
  ofTwoArrows_restrictOpenHom_mem_smallTopology A
    (by rw [← ambientOpen_sup, hV, ambientOpen_top])

/-! ### Mayer--Vietoris for the sections of a sheaf -/

/-- **The sections of a sheaf on `Cris(X/S)` over a cartesian square whose lower edges are
monomorphisms generating a covering sieve form a cartesian square.**  Exactness on the left and in
the middle is the sheaf condition for the covering pair. -/
theorem isPullback_op_map_of_cover {𝒜 : Type v} [Category.{w} 𝒜]
    (sq : Square (CrystallineThickening S)) [Mono sq.f₂₄] [Mono sq.f₃₄]
    (hp : sq.IsPullback) (hc : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ smallTopology S sq.X₄)
    (F : Sheaf (smallTopology S) 𝒜) : (sq.op.map F.obj).IsPullback := by
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ F.property.amalgamateOfArrows _ hc
      (fun j ↦ WalkingPair.casesOn j s.fst s.snd)
      (fun W ↦ by
        rintro (_ | _) (_ | _) a b fac
        · obtain rfl : a = b := (cancel_mono sq.f₂₄).mp fac
          rfl
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac
          exact (congrArg (fun k ↦ s.fst ≫ k) (F.obj.map_comp sq.f₁₂.op φ.op)).trans
            (((Category.assoc _ _ _).symm.trans
              ((s.condition =≫ F.obj.map φ.op).trans (Category.assoc _ _ _))).trans
              (congrArg (fun k ↦ s.snd ≫ k) (F.obj.map_comp sq.f₁₃.op φ.op)).symm)
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac.symm
          exact (congrArg (fun k ↦ s.snd ≫ k) (F.obj.map_comp sq.f₁₃.op φ.op)).trans
            (((Category.assoc _ _ _).symm.trans
              ((s.condition.symm =≫ F.obj.map φ.op).trans (Category.assoc _ _ _))).trans
              (congrArg (fun k ↦ s.fst ≫ k) (F.obj.map_comp sq.f₁₂.op φ.op)).symm)
        · obtain rfl : a = b := (cancel_mono sq.f₃₄).mp fac
          rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
  · apply F.property.hom_ext_ofArrows _ hc
    rintro (_ | _)
    · rwa [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
    · rwa [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]

/-- **Stacks Project, Tag 07ML.**  Mayer--Vietoris for an open covering `X = X' ∪ X''` on the small
crystalline site: for every sheaf `F` on `Cris(X/S)` and every object `(U, T, δ)`, the sections of
`F` over `(U, T, δ)` and over its restrictions to `X'`, `X''` and `X''' = X' ∩ X''` form a
cartesian square.  For a sheaf of abelian groups this is exactness of
`0 ⟶ F(U, T, δ) ⟶ F' ⊕ F'' ⟶ F'''`.

This is the geometric input the remark reduces its distinguished triangle to.  The short exact
form of this square at an injective abelian sheaf is
`CrystallineThickening.openCoverShortComplex_shortExact` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisShortExact.lean`, and the
triangle it yields, at a fixed object of the site, is
`CrystallineThickening.openCoverTriangle_distinguished` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisTriangle.lean`.  What the
remark's own statement still wants is the same sequence for the derived *global* sections of the
four crystalline sites; see the module documentation. -/
@[stacks 07ML "the Mayer-Vietoris square of the covering on Cris(X/S), the fact the remark's
  triangle is a formal consequence of.  The triangle at a fixed object of the site is
  openCoverTriangle_distinguished of SmallSite/MayerVietorisTriangle.lean; the remark's own
  statement, about the derived global sections of the four crystalline sites, is not stated"]
theorem isPullback_sections_openCoverSquare {𝒜 : Type v} [Category.{w} 𝒜]
    (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤)
    (F : Sheaf (smallTopology S) 𝒜) :
    ((openCoverSquare A V₁ V₂).op.map F.obj).IsPullback :=
  isPullback_op_map_of_cover (openCoverSquare A V₁ V₂) (isPullback_openCoverSquare A V₁ V₂)
    (ofTwoArrows_openCoverSquare_mem_smallTopology A hV) F

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
