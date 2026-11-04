module

public import StacksFrontier.Algebra.Homology.Embedding.StupidTruncHomology
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a bounded above complex of finite free summands

Let `(C, O)` be a ringed site, let `E` be a cochain complex of `O`-modules which is bounded
above and whose terms are all direct summands of finite free `O`-modules, and let `F` be a
complex of `O`-modules which is bounded below. Stacks 08I5 asserts that the ordinary internal
Hom complex `SheafHom(E, F)` of Stacks 0A8Z represents the derived internal Hom
`RSheafHom(E, F)`.

The source is *not* assumed strictly perfect here: it may have infinitely many nonzero terms,
so the finite-direct-sum description of the Hom complex is unavailable and Stacks 08JH does not
apply. What replaces it is the stupid filtration of `E` together with the lower bound on the
target: in a fixed degree `n`, the truncation `σ^{≥k}E` for `k = a - n - 1` is bounded, Stacks
08JH applies to it, and the inclusion `σ^{≥k}E ⟶ E` induces a *degreewise isomorphism* of
internal Hom complexes in all degrees `≤ n + 1`, because in the degrees it is not an
isomorphism in the matching term of the target vanishes. Two out of three in degree `n` then
transports the quasi-isomorphy from the truncation to `E` itself.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_boundedAbove_isFiniteFreeSummand`: the
  internal Hom complex out of a bounded above complex of finite free summands carries a
  quasi-isomorphism between two complexes vanishing below a common bound to a
  quasi-isomorphism. This is the whole content of Stacks 08I5.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_boundedAbove`: the
  canonical comparison of `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` from the
  class of `SheafHom(E, F)` to `RSheafHom(E, F)` is an isomorphism, which is the representation
  statement of Stacks 08I5.

## Implementation notes

**Changing the resolution.** The reduction
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_iff` turns the comparison into
the quasi-isomorphy of the map of internal Hom complexes induced by the K-injective
augmentation `F ⟶ I` of the target, where `I = (kInjectiveResolution X).obj F` is the *chosen*
functorial resolution of `Stacks.Injectives.kInjectiveResolutionFunctor`. That resolution is
produced by Spaltenstein's transfinite construction and carries **no** lower bound — its
interface is K-injectivity of the value and quasi-isomorphy of the augmentation and nothing else
— so the quasi-isomorphism invariance above does not apply to it directly.

What repairs this is a change of resolution.
`CochainComplex.exists_injectiveResolution_isStrictlyGE`
(Stacks 013K) gives a degreewise injective resolution `u : F ⟶ I₀` which is again zero below
`a`, and `CochainComplex.isKInjective_of_injective` (Stacks 013R) makes `I₀` K-injective. The
invariance applies to `u`; and `AlgebraicGeometry.RingedSite.homMap_quasiIso` (Stacks 0A95)
applies to any quasi-isomorphism between K-injective complexes, hence both to the augmentation
of `I₀` and to the image of `u` under the resolution functor. Naturality of the augmentation
turns `u` followed by the augmentation of `I₀` into the augmentation of `F` followed by the
image of `u`, and two out of three then gives the augmentation of `F` what it needs. So no
hypothesis on the chosen resolution survives in the statement.

**Why `IsFiniteFreeSummand`.** The predicate `IsStrictlyPerfect` carrying the Stacks 08FL tag
is universe-monomorphic and cannot be mentioned at the universes where the internal Hom complex
lives; `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` is the same condition stated
universe-polymorphically. The reasons are recorded at length in the implementation notes of
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`.

**Statement at the site rather than the space.** Stacks 08I5 is stated for a ringed space. A
ringed space gives a ringed site, and the internal Hom complex of the site restricted to the
site of opens is the internal Hom complex of the space, so stating the result at the ringed site
is the general form; no transport between the two Hom complexes is needed.

## References

* [Stacks Project, Tag 08I5](https://stacks.math.columbia.edu/tag/08I5)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

section Degreewise

variable {E E' F :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Precomposition with a morphism which is either an isomorphism or has zero target is a
bijection on morphism groups. -/
private lemma precomp_bijective_of_isIso_or_isZero {A : Type*} [Category A]
    [HasZeroMorphisms A] {P P' Q : A} (g : P' ⟶ P) (h : IsIso g ∨ IsZero Q) :
    Function.Bijective (fun f : P ⟶ Q => g ≫ f) := by
  rcases h with h | h
  · have := h
    exact ⟨fun _ _ he => (cancel_epi g).mp he, fun f => ⟨inv g ≫ f, by simp⟩⟩
  · exact ⟨fun _ _ _ => h.eq_of_tgt _ _, fun f => ⟨0, h.eq_of_tgt _ _⟩⟩

/-- Precomposing degree-`n` cochains with a morphism of sources is a bijection as soon as, in
every degree `p`, either the morphism is an isomorphism or the degree-`p + n` term of the target
vanishes. The cochains are compared componentwise, where the statement is
`precomp_bijective_of_isIso_or_isZero`. -/
private lemma bijective_cochainConj_precomp (e : E' ⟶ E) (n : ℤ) (U : X.C)
    (he : ∀ p, IsIso (e.f p) ∨ IsZero (F.X (p + n))) :
    Function.Bijective (fun c : Cochain (restrictComplex X E U) (restrictComplex X F U) n =>
      cochainConj X U e (𝟙 F) c) := by
  classical
  have key (c : Cochain (restrictComplex X E U) (restrictComplex X F U) n) (p q : ℤ)
      (hpq : p + n = q) :
      (cochainConj X U e (𝟙 F) c).v p q hpq = (e.f p).over U ≫ c.v p q hpq := by
    rw [cochainConj_v, HomologicalComplex.id_f,
      show SheafOfModules.Hom.over (𝟙 (F.X q)) U = 𝟙 ((restrictComplex X F U).X q) from rfl,
      Category.comp_id]
  have hg (p q : ℤ) (hpq : p + n = q) :
      Function.Bijective (fun f : (restrictComplex X E U).X p ⟶ (restrictComplex X F U).X q =>
        (e.f p).over U ≫ f) := by
    refine precomp_bijective_of_isIso_or_isZero _ ?_
    rcases he p with h | h
    · have := h
      exact Or.inl
        (inferInstanceAs (IsIso ((SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map (e.f p))))
    · subst hpq
      exact Or.inr
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero h)
  constructor
  · intro c c' hcc
    refine Cochain.ext _ _ fun p q hpq => ?_
    refine (hg p q hpq).1 ?_
    exact (key c p q hpq).symm.trans ((congrArg
      (fun z : Cochain (restrictComplex X E' U) (restrictComplex X F U) n => z.v p q hpq)
        hcc).trans (key c' p q hpq))
  · intro t
    refine ⟨Cochain.mk fun p q hpq => ((hg p q hpq).2 (t.v p q hpq)).choose, ?_⟩
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [key _ p q hpq, Cochain.mk_v]
    exact ((hg p q hpq).2 (t.v p q hpq)).choose_spec

/-- The map of internal Hom complexes induced by a morphism `e` of sources is an isomorphism in
degree `n` as soon as, in every degree `p`, either `e` is an isomorphism or the degree-`p + n`
term of the target vanishes.

This is `bijective_cochainConj_precomp` read through
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`, which turns it into bijectivity on
sections over every object of the site; a morphism of sheaves of modules whose sections maps are
all bijective is an isomorphism. -/
private lemma isIso_homMap_f_of_isIso_or_isZero (e : E' ⟶ E) (n : ℤ)
    (he : ∀ p, IsIso (e.f p) ∨ IsZero (F.X (p + n))) :
    IsIso ((homMap X e (𝟙 F)).f n) := by
  have hsec : ∀ V : X.Cᵒᵖ, IsIso (((homMap X e (𝟙 F)).f n).val.app V) := by
    rintro ⟨U⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    show Function.Bijective (fun s : ((sheafHomComplex X E F).obj.X n).val.obj (op U) =>
      ((homMap X e (𝟙 F)).f n).val.app (op U) s)
    exact ((sheafHomComplex X E' F).sectionsEquiv U n).symm.bijective.comp
      ((bijective_cochainConj_precomp X e n U he).comp
        ((sheafHomComplex X E F).sectionsEquiv U n).bijective)
  have hpre : IsIso ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map
      ((SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((homMap X e (𝟙 F)).f n))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    have := hsec V
    show IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      (((homMap X e (𝟙 F)).f n).val.app V))
    infer_instance
  have hval : IsIso ((SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      ((homMap X e (𝟙 F)).f n)) :=
    isIso_of_reflects_iso _
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  exact (SheafOfModules.fullyFaithfulForget
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).isIso_of_isIso_map _

end Degreewise

section StupidTruncation

/-- **The inclusion of a stupid truncation of the source is a degree-`n` quasi-isomorphism of
internal Hom complexes.** If the target vanishes below `a` and `k + n + 1 ≤ a`, then the
inclusion `σ^{≥k}E ⟶ E` induces a map of internal Hom complexes which is an isomorphism in all
three degrees `n - 1`, `n` and `n + 1` computing the degree-`n` cohomology: in a degree
`m ≤ n + 1` and a source degree `p < k` the matching target degree `p + m` is below `a`, while
for `p ≥ k` the inclusion is itself an isomorphism. -/
private lemma quasiIsoAt_homMap_ιStupidTrunc
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a k n : ℤ)
    (hF : ∀ p, p < a → IsZero (F.X p)) (hkn : k + n + 1 ≤ a) :
    QuasiIsoAt (homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 F)) n := by
  have hiso (m : ℤ) (hm : m ≤ n + 1) :
      IsIso ((homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 F)).f m) := by
    refine isIso_homMap_f_of_isIso_or_isZero X _ m fun p => ?_
    by_cases hp : k ≤ p
    · exact Or.inl (E.isIso_ιStupidTrunc_embeddingUpIntGE_f k p hp)
    · exact Or.inr (hF (p + m) (by omega))
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let S := (HomologicalComplex.shortComplexFunctor'
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) (n - 1) n (n + 1)).map
    (homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 F))
  have h₁ : IsIso S.τ₁ := hiso (n - 1) (by omega)
  have h₂ : IsIso S.τ₂ := hiso n (by omega)
  have h₃ : IsIso S.τ₃ := hiso (n + 1) (by omega)
  have hS : IsIso S := ShortComplex.isIso_of_isIso S
  exact inferInstanceAs (ShortComplex.QuasiIso S)

end StupidTruncation

section Main

variable (E F G :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The degreewise form of Stacks 08I5: with `E` bounded above by `b` and both targets
vanishing below `a`, the induced map of internal Hom complexes is a quasi-isomorphism in the
single degree `n`, provided `k + n + 1 ≤ a`.

The truncation `σ^{≥k}E` is zero below `k` and, through the inclusion, zero above `b`, so it is
bounded and `homMap_quasiIso_of_bounded` (Stacks 08JH) applies to it. The inclusion induces
degree-`n` quasi-isomorphisms on both internal Hom complexes by
`quasiIsoAt_homMap_ιStupidTrunc`, and the square of induced maps commutes by `homMap_comp`, so
two out of three gives the claim. -/
private lemma quasiIsoAt_homMap_of_boundedAbove (a k n b : ℤ)
    (hF : ∀ i, i < a → IsZero (F.X i))
    (hG : ∀ i, i < a → IsZero (G.X i))
    (hb : ∀ i, b < i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i))
    (hkn : k + n + 1 ≤ a)
    (f : F ⟶ G) [QuasiIso f] :
    QuasiIsoAt (homMap X (𝟙 E) f) n := by
  have hlo (i : ℤ) (hi : i < k) :
      IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i) :=
    E.isZero_X_stupidTrunc_embeddingUpIntGE k i hi
  have hι (i : ℤ) (hi : k ≤ i) :
      (E.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i ≅ E.X i :=
    haveI := E.isIso_ιStupidTrunc_embeddingUpIntGE_f k i hi
    asIso ((E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).f i)
  have hhi (i : ℤ) (hi : k + ((b - k + 1).toNat : ℤ) ≤ i) :
      IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i) :=
    IsZero.of_iso (hb i (by omega)) (hι i (by omega))
  have hterm' (i : ℤ) :
      IsFiniteFreeSummand X ((E.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i) := by
    by_cases hi : k ≤ i
    · exact IsFiniteFreeSummand.of_iso X (hι i hi) (hterm i)
    · exact IsFiniteFreeSummand.of_isZero X (hlo i (by omega))
  have hbdd : QuasiIso (homMap X (𝟙 (E.stupidTrunc (ComplexShape.embeddingUpIntGE k))) f) :=
    homMap_quasiIso_of_bounded X f (b - k + 1).toNat k _ hlo hhi hterm'
  have hFt : QuasiIsoAt (homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 F)) n :=
    quasiIsoAt_homMap_ιStupidTrunc X E F a k n hF hkn
  have hGt : QuasiIsoAt (homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 G)) n :=
    quasiIsoAt_homMap_ιStupidTrunc X E G a k n hG hkn
  have hcomm : homMap X (𝟙 E) f ≫
      homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 G) =
      homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 F) ≫
        homMap X (𝟙 (E.stupidTrunc (ComplexShape.embeddingUpIntGE k))) f := by
    rw [homMap_comp, homMap_comp]
    simp
  have hcomp : QuasiIsoAt (homMap X (𝟙 E) f ≫
      homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 G)) n := by
    rw [hcomm]
    exact quasiIsoAt_comp _ _ n
  exact quasiIsoAt_of_comp_right (homMap X (𝟙 E) f)
    (homMap X (E.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (𝟙 G)) n

/-- **Stacks 08I5**, the quasi-isomorphism invariance. Let `E` be a complex of `O`-modules which
is bounded above and all of whose terms are direct summands of finite free `O`-modules. Then the
internal Hom complex out of `E` carries a quasi-isomorphism between two complexes vanishing in
all degrees below a common bound `a` to a quasi-isomorphism.

This is the whole content of the tag; the representation statement
`strictlyPerfectHomComparison_isIso_of_boundedAbove` is obtained from it by the formal reduction
`strictlyPerfectHomComparison_isIso_iff`.

Unlike `homMap_quasiIso_of_isFiniteFreeSummand` (Stacks 08JH) the source is not assumed to have
finitely many nonzero terms, and in exchange the targets are assumed bounded below. The proof is
degreewise: `quasiIsoAt_homMap_of_boundedAbove` at `k = a - n - 1`. -/
@[stacks 08I5 "invariance of the internal Hom complex under quasi-isomorphism"]
theorem homMap_quasiIso_of_boundedAbove_isFiniteFreeSummand (a : ℤ)
    (hF : ∀ i, i < a → IsZero (F.X i))
    (hG : ∀ i, i < a → IsZero (G.X i))
    (hE : ∃ b : ℤ, ∀ i, b < i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i))
    (f : F ⟶ G) [QuasiIso f] :
    QuasiIso (homMap X (𝟙 E) f) := by
  obtain ⟨b, hb⟩ := hE
  exact (quasiIso_iff _).2 fun n =>
    quasiIsoAt_homMap_of_boundedAbove X E F G a (a - n - 1) n b hF hG hb hterm (by omega) f

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **Stacks 08I5**, the representation statement. Let `E` be a complex of `O`-modules which is
bounded above and all of whose terms are direct summands of finite free `O`-modules, and let `F`
vanish in all degrees below `a`. Then the derived internal Hom `RSheafHom(E, F)` is represented
by the ordinary internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z, the comparison being the
canonical one of `strictlyPerfectHomComparison`.

By `strictlyPerfectHomComparison_isIso_iff` the claim is the quasi-isomorphy of the map of
internal Hom complexes induced by the K-injective augmentation `F ⟶ I` of the target. The
chosen resolution `I` carries no lower bound, so the invariance is applied instead to a
degreewise injective resolution `u : F ⟶ I₀` which is again zero below `a`, and transported to
the augmentation of `F` along the naturality square of the augmentation; the two maps between
K-injective complexes occurring there are handled by `homMap_quasiIso` (Stacks 0A95). See the
implementation notes. -/
@[stacks 08I5 "representation of derived internal Hom by the ordinary Hom complex"]
theorem strictlyPerfectHomComparison_isIso_of_boundedAbove (a : ℤ)
    (hF : ∀ i, i < a → IsZero (F.X i))
    (hE : ∃ b : ℤ, ∀ i, b < i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    IsIso (strictlyPerfectHomComparison X D E F) := by
  have hGE : F.IsStrictlyGE a :=
    ⟨fun i hi => hF i (by
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi)⟩
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a F
  have := hR
  have hKI : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex a
  have hKI' : ((Functor.id (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)).obj
      R.cocomplex).IsKInjective := hKI
  have h1 : QuasiIso (homMap X (𝟙 E) R.ι) :=
    homMap_quasiIso_of_boundedAbove_isFiniteFreeSummand X E F R.cocomplex a hF
      (fun i hi => R.cocomplex.isZero_of_isStrictlyGE a i hi) hE hterm R.ι
  have h2 : QuasiIso (homMap X (𝟙 E) ((kInjectiveAugmentation X).app R.cocomplex)) :=
    homMap_quasiIso X ((kInjectiveAugmentation X).app R.cocomplex) (𝟙 E)
  have : QuasiIso ((kInjectiveResolution X).map R.ι) := quasiIso_kInjectiveResolution_map X R.ι
  have h3 : QuasiIso (homMap X (𝟙 E) ((kInjectiveResolution X).map R.ι)) :=
    homMap_quasiIso X ((kInjectiveResolution X).map R.ι) (𝟙 E)
  have hnat : R.ι ≫ (kInjectiveAugmentation X).app R.cocomplex =
      (kInjectiveAugmentation X).app F ≫ (kInjectiveResolution X).map R.ι :=
    (kInjectiveAugmentation X).naturality R.ι
  have heq : homMap X (𝟙 E) ((kInjectiveAugmentation X).app F) ≫
      homMap X (𝟙 E) ((kInjectiveResolution X).map R.ι) =
      homMap X (𝟙 E) R.ι ≫
        homMap X (𝟙 E) ((kInjectiveAugmentation X).app R.cocomplex) := by
    rw [homMap_comp, homMap_comp, hnat]
  have hcomp : QuasiIso (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F) ≫
      homMap X (𝟙 E) ((kInjectiveResolution X).map R.ι)) := by
    rw [heq]
    exact quasiIso_comp _ _
  exact (strictlyPerfectHomComparison_isIso_iff X D E F).2
    (quasiIso_of_comp_right _ (homMap X (𝟙 E) ((kInjectiveResolution X).map R.ι)))

end Main

end AlgebraicGeometry.RingedSite

end
