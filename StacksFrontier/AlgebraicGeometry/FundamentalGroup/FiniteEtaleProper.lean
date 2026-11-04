module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.Pair

/-!
# Finite étale covers of a proper scheme over a henselian pair

For a scheme `X` this file introduces the category `FiniteEtaleOver X` of schemes finite étale
over `X` (the category usually written `FÉt_X`) and the base-change functor
`finiteEtaleBaseChange f : FiniteEtaleOver Y ⥤ FiniteEtaleOver X` attached to a morphism
`f : X ⟶ Y`.

The theorem of Gabber and Elkik (Stacks Tag 0GS2) says that if `(A, I)` is a henselian pair and
`X` is proper over `Spec A`, then base change along the closed immersion
`X₀ = X ×_{Spec A} Spec (A ⧸ I) ⟶ X` is an *equivalence* of categories. The half of that statement
which does not need algebraization is proved here: the functor is **faithful**. The mechanism is
purely geometric and is isolated in
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes`: if every point of
`X` specializes into the image of `g : X₀ ⟶ X`, then base change along `g` is faithful on finite
étale covers. Indeed, two morphisms `U ⟶ V` over `X` that agree over `X₀` agree on the preimage of
the diagonal of `V ⟶ X`, which is an *open* subscheme of `U` because `V ⟶ X` is étale; an open set
that meets the closure of a point contains that point, and every point of `U` specializes into the
closed fibre because `U` is proper over `A`.

That `X` proper over a henselian pair `(A, I)` has every point specializing into the closed fibre
is `AlgebraicGeometry.exists_specializes_mem_range_pullback_fst_of_isProper`; the only input from
the henselian pair is that `I` is contained in the Jacobson radical of `A`, so that every prime of
`A` is contained in a maximal ideal containing `I`.

## Main definitions

* `AlgebraicGeometry.finiteEtale` — the property that a morphism of schemes is finite and étale.
* `AlgebraicGeometry.FiniteEtaleOver` — the category of schemes finite étale over a scheme.
* `AlgebraicGeometry.finiteEtaleBaseChange` — the canonical base-change functor on these
  categories.

## Main results

* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes` — base change
  along a morphism whose image receives every point as a specialization is faithful.
* `AlgebraicGeometry.exists_specializes_mem_range_pullback_fst_of_isProper` — every point of a
  scheme proper over `A` specializes into the fibre over `V(I)`, when `I` is contained in the
  Jacobson radical of `A`.
* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_isProper_of_henselianPair` — the
  faithfulness half of Tag 0GS2.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
-/

@[expose] public section

open CategoryTheory Limits

universe u

/-- If `π` is a closed map and every point of the target specializes into `Z`, then every point of
the source specializes into `π ⁻¹' Z`. -/
theorem IsClosedMap.exists_specializes_mem_preimage {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {π : α → β} (hπ : IsClosedMap π) {Z : Set β}
    (hZ : ∀ y : β, ∃ z ∈ Z, y ⤳ z) (x : α) :
    ∃ x' ∈ π ⁻¹' Z, x ⤳ x' := by
  obtain ⟨z, hzZ, hz⟩ := hZ (π x)
  have hcl : IsClosed (π '' closure {x}) := hπ _ isClosed_closure
  have hmem : π x ∈ π '' closure {x} := ⟨x, subset_closure rfl, rfl⟩
  have hz' : z ∈ π '' closure {x} :=
    hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
      (specializes_iff_mem_closure.mp hz)
  obtain ⟨x', hx', rfl⟩ := hz'
  exact ⟨x', hzZ, specializes_iff_mem_closure.mpr hx'⟩

/-- If the ideal `I` is contained in the Jacobson radical of `A`, then every point of `Spec A`
specializes into the closed subset `V(I)`: a maximal ideal containing a given prime automatically
contains `I`. -/
@[ega "I 1.1.15"]
theorem PrimeSpectrum.exists_specializes_mem_zeroLocus_of_le_jacobson {A : Type*} [CommRing A]
    {I : Ideal A} (hI : I ≤ (⊥ : Ideal A).jacobson) (p : PrimeSpectrum A) :
    ∃ q ∈ PrimeSpectrum.zeroLocus (I : Set A), p ⤳ q := by
  obtain ⟨m, hm, hle⟩ := p.asIdeal.exists_le_maximal p.2.ne_top
  refine ⟨⟨m, hm.isPrime⟩, ?_, (PrimeSpectrum.le_iff_specializes _ _).mp hle⟩
  rw [PrimeSpectrum.mem_zeroLocus]
  exact hI.trans (by rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hm⟩)

namespace AlgebraicGeometry

/-- The property that a morphism of schemes is both finite and étale. -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

/-- Finite étale morphisms contain the identities and are stable under composition. -/
instance : MorphismProperty.IsMultiplicative (finiteEtale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.inf

/-- Finite étale morphisms are stable under base change. -/
instance :
    MorphismProperty.IsStableUnderBaseChange (finiteEtale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Finite étale morphisms cancel on the right: if `g` and `f ≫ g` are finite étale, so is `f`.
For the finiteness half this uses that a finite morphism is separated, and for the étale half
that an étale morphism is unramified. -/
instance : MorphismProperty.HasOfPostcompProperty
    (finiteEtale : MorphismProperty Scheme.{u}) finiteEtale where
  of_postcomp f g hg hfg :=
    ⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g
        (by have := hg.1; infer_instance) hfg.1,
      MorphismProperty.of_postcomp @Etale (W' := @Etale) f g hg.2 hfg.2⟩

/-- The category of schemes finite étale over `X`, usually written `FÉt_X`. -/
abbrev FiniteEtaleOver (X : Scheme.{u}) :=
  MorphismProperty.Over (finiteEtale : MorphismProperty Scheme.{u}) ⊤ X

/-- The canonical base-change functor between categories of finite étale schemes. -/
noncomputable def finiteEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FiniteEtaleOver Y ⥤ FiniteEtaleOver X :=
  MorphismProperty.Over.pullback (finiteEtale : MorphismProperty Scheme.{u}) ⊤ f

/-- Base change replaces a finite étale cover `A ⟶ Y` by the chosen pullback `A ×_Y X`. -/
theorem finiteEtaleBaseChange_obj_left {X Y : Scheme.{u}} (f : X ⟶ Y) (A : FiniteEtaleOver Y) :
    ((finiteEtaleBaseChange f).obj A).left = pullback A.hom f :=
  rfl

/-- The first projection of the pullback is natural in the finite étale cover: base change of a
morphism `φ` of finite étale covers of `Y`, followed by the projection to the cover of `Y`, is the
projection followed by `φ`. -/
theorem finiteEtaleBaseChange_map_left_fst {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : FiniteEtaleOver Y} (φ : A ⟶ B) :
    ((finiteEtaleBaseChange f).map φ).left ≫ pullback.fst B.hom f
      = pullback.fst A.hom f ≫ φ.left :=
  pullback.lift_fst _ _ _

/-- **Faithfulness of base change on finite étale covers.** Let `g : X₀ ⟶ X` be a morphism of
schemes such that every point of `X` specializes into the image of `g`. Then base change along `g`
is faithful on finite étale covers.

Two morphisms `U ⟶ V` over `X` that become equal after base change agree on the preimage of the
diagonal of `V ⟶ X`. That preimage is open, because the diagonal of an étale morphism is an open
immersion, and it contains the whole of `X₀ ×_X U`; since `U ⟶ X` is finite, hence closed, every
point of `U` specializes into that closed fibre, and an open set containing a specialization of a
point contains the point itself. -/
theorem faithful_finiteEtaleBaseChange_of_forall_exists_specializes {X X₀ : Scheme.{u}}
    (g : X₀ ⟶ X) (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') :
    (finiteEtaleBaseChange g).Faithful := by
  refine ⟨fun {U V} φ ψ h => ?_⟩
  have hUfin : IsFinite U.hom := U.prop.1
  have hVet : Etale V.hom := V.prop.2
  have hkey : pullback.fst U.hom g ≫ φ.left = pullback.fst U.hom g ≫ ψ.left := by
    rw [← finiteEtaleBaseChange_map_left_fst g φ, ← finiteEtaleBaseChange_map_left_fst g ψ, h]
  have hw : φ.left ≫ V.hom = ψ.left ≫ V.hom := by
    rw [MorphismProperty.Over.w, MorphismProperty.Over.w]
  have hfac : pullback.fst U.hom g ≫ pullback.lift φ.left ψ.left hw
      = (pullback.fst U.hom g ≫ φ.left) ≫ pullback.diagonal V.hom := by
    apply pullback.hom_ext
    · simp [pullback.lift_fst]
    · simp [pullback.lift_snd, hkey]
  have hopen : IsOpen ((pullback.lift φ.left ψ.left hw).base ⁻¹'
      Set.range (pullback.diagonal V.hom).base) :=
    (IsOpenImmersion.isOpen_range (pullback.diagonal V.hom)).preimage
      (pullback.lift φ.left ψ.left hw).base.hom.continuous
  have hsub : Set.range (pullback.fst U.hom g).base ⊆
      (pullback.lift φ.left ψ.left hw).base ⁻¹' Set.range (pullback.diagonal V.hom).base := by
    rintro x ⟨y, rfl⟩
    exact ⟨(pullback.fst U.hom g ≫ φ.left).base y, by
      simpa using (congrArg (fun k => k.base y) hfac).symm⟩
  have hall : Set.range (pullback.lift φ.left ψ.left hw).base
      ⊆ Set.range (pullback.diagonal V.hom).base := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨u', hu', hspec⟩ := U.hom.isClosedMap.exists_specializes_mem_preimage hsp u
    refine hspec.mem_open hopen (hsub ?_)
    rw [Scheme.Pullback.range_fst]
    exact hu'
  obtain ⟨l, hl⟩ : ∃ l : U.left ⟶ V.left,
      l ≫ pullback.diagonal V.hom = pullback.lift φ.left ψ.left hw :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hall⟩
  apply MorphismProperty.Over.Hom.ext
  have h1 : φ.left = l := by
    simpa [pullback.lift_fst] using (congrArg (· ≫ pullback.fst V.hom V.hom) hl).symm
  have h2 : ψ.left = l := by
    simpa [pullback.lift_snd] using (congrArg (· ≫ pullback.snd V.hom V.hom) hl).symm
  rw [h1, h2]

/-- If `I` is contained in the Jacobson radical of `A` and `X` is proper over `Spec A`, then every
point of `X` specializes into the closed fibre `X ×_{Spec A} Spec (A ⧸ I)`. -/
theorem exists_specializes_mem_range_pullback_fst_of_isProper (A : Type u) [CommRing A]
    {I : Ideal A} (hI : I ≤ (⊥ : Ideal A).jacobson) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] (x : X) :
    ∃ x' ∈ Set.range
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base, x ⤳ x' := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base
      = PrimeSpectrum.zeroLocus (I : Set A) := by
    show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have hZ : ∀ y : Spec (CommRingCat.of A),
      ∃ z ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base, y ⤳ z := by
    intro y
    rw [hr]
    exact PrimeSpectrum.exists_specializes_mem_zeroLocus_of_le_jacobson hI y
  have hx := f.isClosedMap.exists_specializes_mem_preimage hZ x
  rwa [← Scheme.Pullback.range_fst] at hx

/-- **The faithfulness half of Stacks Project, Tag 0GS2.** If `(A, I)` is a henselian pair and `X`
is proper over `Spec A`, then pullback from `X` to `X ×_{Spec A} Spec (A ⧸ I)` is faithful on
finite étale schemes.

Fullness and essential surjectivity are the deep halves of Tag 0GS2: the Stacks proof deduces
fullness from essential surjectivity, and essential surjectivity rests on Grothendieck's
algebraization theorem together with Artin approximation over a Noetherian G-ring. -/
theorem faithful_finiteEtaleBaseChange_of_isProper_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).Faithful :=
  faithful_finiteEtaleBaseChange_of_forall_exists_specializes _
    (exists_specializes_mem_range_pullback_fst_of_isProper A hI.le_jacobson f)

end AlgebraicGeometry

end
