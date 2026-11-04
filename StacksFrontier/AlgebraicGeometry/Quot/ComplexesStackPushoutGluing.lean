module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutLegFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonCocone

/-!
# `Complexes_{X/B}` at a pushout along a thickening: essential surjectivity (Stacks 0DLK)

This file is the second half of the proof of Stacks 0DLK, essential surjectivity of
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` for a
pushout `Y' = Y ⨿_Z Z'` along a finite order thickening `Z ⟶ Z'` and an affine `Z ⟶ Y`.

The three results the source's proof cites for this half and which the library does not yet
have, Stacks 07W3, 0DL7 and 0DL4 (not yet proved here), are explicit
hypotheses `h07W3`, `h0DL7`, `h0DL4`, each stated at the content of its tag at the instance the
proof uses; everything else is proved. Together with the full faithfulness half of
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackPushout.lean` (from Stacks 0DLG, pending) this
gives Stacks 0DLK and the hypothesis `h0DLK` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`. Nothing here
is registered.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.essSurj_complexesFiberSquareComparison`: the
  essential surjectivity half of Stacks 0DLK, from Stacks 07W3, 0DL7 and 0DL4.
* `AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison`:
  Stacks 0DLK, from Stacks 0DLG, 07W3, 0DL7 and 0DL4.
* `AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor` and
  `AlgebraicGeometry.Space.ComplexesSituation.satisfiesRS_complexesFunctor`: conditions (RS*)
  and (RS) for `Complexes_{X/B}`, from the same four.
* `AlgebraicGeometry.Space.exists_lift_of_isFieldObject`: a field-valued point lifts through a
  finite order thickening of test schemes.
* `Stacks.Thickenings.ker_le_ker_of_isFiniteOrderThickening`: a morphism from a reduced scheme
  factors through every finite order thickening of its target.
* `CategoryTheory.PullbackData.heq_fibreComp_triangle`: the composites of a gluing along two
  equal factorizations agree.

## References

* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {Dat : A → Type u₂} [∀ a, Category.{v₂} (Dat a)]

/-- **The comparison of two glued composites.** Let `P` be a pullback datum, `l ≫ n` and
`k ≫ m` two equal composites, `N` an object over their common target, and `cQ : n^*N ⟶ M`,
`cP : m^*N ⟶ K`, `a : l^*M ⟶ U`, `bb : k^*K ⟶ U` morphisms, `bb` invertible. If `cQ` and `cP`
are compatible with `a ≫ inv bb` through the comparison `l^*n^*N ≅ k^*m^*N`, then the two
composites `(l ≫ n)^*N ⟶ U` and `(k ≫ m)^*N ⟶ U` agree, up to the identification of their
sources. These are the composites of a category of pairs (test object, module) whose morphisms
carry a comparison of the pulled back module, as in Stacks 0DLE: this is what makes a gluing
compatible with the two restrictions. -/
theorem heq_fibreComp_triangle (P : PullbackData A Dat) {p q p' q' : A} {l : p ⟶ q}
    {n : q ⟶ q'} {k : p ⟶ p'} {m : p' ⟶ q'} {g₁ g₂ : p ⟶ q'} (h₁ : l ≫ n = g₁)
    (h₂ : k ≫ m = g₂) (hg : g₁ = g₂) (hw : l ≫ n = k ≫ m) {N : Dat q'} {M : Dat q}
    {K : Dat p'} {U : Dat p} (a : (P.pull l).obj M ⟶ U) (bb : (P.pull k).obj K ⟶ U) [hbb : IsIso bb]
    (cQ : (P.pull n).obj N ⟶ M) (cP : (P.pull m).obj N ⟶ K)
    (hcompat : (P.pull l).map cQ ≫ a ≫ inv bb =
      (P.compIso l n).inv.app N ≫ eqToHom (congrArg (fun g => (P.pull g).obj N) hw) ≫
        (P.compIso k m).hom.app N ≫ (P.pull k).map cP) :
    HEq (Functor.fibreComp (P.triangle h₁) a cQ) (Functor.fibreComp (P.triangle h₂) bb cP) := by
  subst hg h₁
  have h2 := hcompat =≫ bb
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h2
  refine heq_of_eq ?_
  rw [Functor.fibreComp, Functor.fibreComp, triangle_rfl, h2, triangle_eq]
  simp

end CategoryTheory.PullbackData

namespace Stacks.Thickenings

/-- **A morphism from a reduced scheme factors through a finite order thickening.** If
`b : X ⟶ X'` is a finite order thickening and `K` is reduced, the kernel of `b` is contained in
the kernel of every `y : K ⟶ X'`: a section of the kernel of `b` over an affine open is
nilpotent, hence dies in the reduced ring of sections of `K`. So `y` lifts through `b`
(`AlgebraicGeometry.IsClosedImmersion.lift`). -/
theorem ker_le_ker_of_isFiniteOrderThickening {K X X' : Scheme.{u}} [IsReduced K]
    {b : X ⟶ X'} (hb : IsFiniteOrderThickening b) (y : K ⟶ X') : b.ker ≤ y.ker := by
  obtain ⟨-, n, hn⟩ := hb
  refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U x hx => ?_
  have hpow : x ^ (n + 1) = 0 := by
    have hmem : x ^ (n + 1) ∈ (b.ker ^ (n + 1)).ideal U := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact Ideal.pow_mem_pow hx _
    rw [hn] at hmem
    simpa using hmem
  have hnil : IsNilpotent ((y.app U).hom x) := ⟨n + 1, by rw [← map_pow, hpow, map_zero]⟩
  exact hnil.eq_zero

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inclusion of algebraic spaces into presheaves preserves fibre products. -/
private theorem preservesPullback_ι_algebraicSpaces {Y Z T : AlgebraicSpaces B S hS}
    (f : Y ⟶ T) (g : Z ⟶ T) :
    PreservesLimit (cospan f g) (ObjectProperty.ι (IsAlgebraicSpace B S hS)) :=
  preservesLimit_of_preserves_limit_cone
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).isLimit
    ((isLimitMapConePullbackConeEquiv _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w).symm
        (IsPullback.of_hasPullback f.hom g.hom).isLimit)

/-- A cartesian square of algebraic spaces is a cartesian square of presheaves. -/
theorem isPullback_hom_of_isPullback_spaces {P Q R T : AlgebraicSpaces B S hS} {k : P ⟶ Q}
    {l : P ⟶ R} {m : Q ⟶ T} {n : R ⟶ T} (sq : IsPullback k l m n) :
    IsPullback k.hom l.hom m.hom n.hom :=
  have := preservesPullback_ι_algebraicSpaces m n
  sq.map (ObjectProperty.ι _)

/-- **A field-valued point lifts through a finite order thickening.** Let `ξ : T ⟶ T'` be a
morphism of test schemes over an algebraic space `Y₀` whose underlying morphism of schemes is a
finite order thickening, and let `T₀` be a test scheme whose underlying scheme is the spectrum of
a field. Then every `y : T₀ ⟶ T'` factors as `y' ≫ ξ`.

The spectrum of a field is reduced, so the kernel of `ξ` is contained in that of `y`
(`Stacks.Thickenings.ker_le_ker_of_isFiniteOrderThickening`), and `y` lifts through the closed
immersion `ξ`; the lift is a morphism over `S` and over `Y₀` because `ξ` is. -/
theorem exists_lift_of_isFieldObject {Y₀ : AlgebraicSpaces B S hS}
    {T₀ T T' : CostructuredArrow (schemeSpaceFunctor B S hS) Y₀} (ξ : T ⟶ T')
    (hξ : Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B S hS).map ξ.left))
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) (y : T₀ ⟶ T') :
    ∃ y' : T₀ ⟶ T, y' ≫ ξ = y := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hT₀
  let : Field k := hk
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj T₀.left) :=
    isReduced_of_isOpenImmersion e.hom
  have := hξ.1
  let v := IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map ξ.left)
    ((BigFppfOver.toScheme B S hS).map y.left)
    (Stacks.Thickenings.ker_le_ker_of_isFiniteOrderThickening hξ _)
  have hv : v ≫ (BigFppfOver.toScheme B S hS).map ξ.left =
      (BigFppfOver.toScheme B S hS).map y.left := IsClosedImmersion.lift_fac _ _ _
  have hvS : v ≫ B.inclusion.map T.left.hom = B.inclusion.map T₀.left.hom := by
    have hξS := congrArg B.inclusion.map (Over.w ξ.left)
    have hyS := congrArg B.inclusion.map (Over.w y.left)
    rw [Functor.map_comp] at hξS hyS
    rw [← hξS, ← Category.assoc]
    exact (congrArg (· ≫ B.inclusion.map T'.left.hom) hv).trans hyS
  let yl : T₀.left ⟶ T.left := BigFppfOver.homOfCompEq B S hS v hvS
  have hyl : yl ≫ ξ.left = y.left :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq, hv])
  refine ⟨CostructuredArrow.homMk yl ?_, ?_⟩
  · rw [← CostructuredArrow.w ξ, ← Category.assoc, ← Functor.map_comp, hyl,
      CostructuredArrow.w y]
  · exact CostructuredArrow.hom_ext _ _ (by simpa using hyl)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

/-- **Two composites of `Complexes_{X/B}` agree when the second factors glue.** Let
`α : u ⟶ x`, `β : u ⟶ y`, `ξ : x ⟶ z` and `η : y ⟶ z` be morphisms of `Complexes_{X/B}` whose
base maps form a commutative square. If the comparisons of complexes of `ξ` and `η` are
compatible with the isomorphism `L(X_α)^*E_x ≅ L(X_β)^*E_y` they induce through the comparison
`L(X_α)^*L(X_ξ)^* ≅ L(X_β)^*L(X_η)^*` of the commutative square of base changes, then
`α ≫ ξ = β ≫ η`. -/
theorem complexesHom_comp_eq_comp_of_compat {D : ComplexesSituation B S hS}
    {u x y z : ComplexesObject D} (α : ComplexesHom u x) (β : ComplexesHom u y)
    (ξ : ComplexesHom x z) (η : ComplexesHom y z) (hbase : α.base ≫ ξ.base = β.base ≫ η.base)
    (hw : D.relativeMap α.base ≫ D.relativeMap ξ.base =
      D.relativeMap β.base ≫ D.relativeMap η.base)
    (hcompat : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap α.base)).map
        ξ.fibre ≫ α.fibre ≫ inv β.fibre (I := β.isIso_fibre) =
      ((smallEtaleDerivedPullbackData B S hS).compIso (D.relativeMap α.base)
          (D.relativeMap ξ.base)).inv.app z.E ≫
        eqToHom (congrArg (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj z.E)
          hw) ≫
        ((smallEtaleDerivedPullbackData B S hS).compIso (D.relativeMap β.base)
          (D.relativeMap η.base)).hom.app z.E ≫
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β.base)).map η.fibre) :
    α.comp ξ = β.comp η := by
  have key := PullbackData.heq_fibreComp_triangle (smallEtaleDerivedPullbackData B S hS)
    (baseChangeMap_comp D.f α.base ξ.base).symm (baseChangeMap_comp D.f β.base η.base).symm
    (congrArg D.relativeMap hbase) hw α.fibre β.fibre (hbb := β.isIso_fibre) ξ.fibre η.fibre
    hcompat
  exact complexesHom_eq_of_heq hbase key

/-- **Stacks 0DLK, the essential surjectivity half.** In Situation 0DLE, let `i ≫ a = f ≫ b` be
a commutative square of the site whose image in schemes is a pushout `Y' = Y ⨿_Z Z'` along the
finite order thickening `i : Z ⟶ Z'` and the affine morphism `f : Z ⟶ Y`. Then the functor
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is
essentially surjective, granted the three results the source's proof cites and which are not yet
in the library, each stated at exactly the instance the proof uses:

* `h07W3`: **Stacks 07W3** (not yet proved here), the counit clause: for a
  pushout `Y'` along a thickening and an affine morphism, which is also the pushout in algebraic
  spaces by Stacks 07SY, and an algebraic space `W` flat over `Y'`, the base change square
  `W_Z ⟶ W_{Z'}`, `W_Z ⟶ W_Y`, `W_{Z'} ⟶ W`, `W_Y ⟶ W` is a pushout of algebraic spaces. It is
  stated for test schemes `Z, Z', Y, Y'`, which is the case the proof applies it to;
* `h0DL7`: **Stacks 0DL7** (not yet proved here), for a pushout of algebraic spaces along a
  thickening `k` and an affine morphism `l`: a triple `(M, K', α)` of pseudo-coherent objects
  and an isomorphism `α : Ll^*M ≅ Lk^*K'` is the restriction of an object `N` of the pushout,
  through isomorphisms `Ln^*N ≅ M` and `Lm^*N ≅ K'` compatible with `α`;
* `h0DL4`: **Stacks 0DL4** (not yet proved here), for the cartesian square of base changes
  `X_T ⟶ X_{T'}` over a finite order thickening `T ⟶ T'` of test schemes, the projection
  `X_{T'} ⟶ T'` being flat and of finite presentation: an object of `D(𝒪_{X_{T'}})` whose
  derived restriction to `X_T` is `T`-perfect is `T'`-perfect. The derived restriction is taken
  up to isomorphism, `T`-perfectness being invariant under isomorphism (Stacks 0DKR).

The proof is the source's. The morphisms `Y ⟶ B` and `Z' ⟶ B` glue to `Y' ⟶ B` because `Y'` is
the pushout in algebraic spaces (Stacks 07SY,
`AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom'`). The base
changes form a pushout `X_{Y'} = X_Y ⨿_{X_Z} X_{Z'}` (`h07W3`) along the thickening
`X_Z ⟶ X_{Z'}` (`AlgebraicGeometry.Space.isThickeningHom_of_isPullback`, a base change of
the thickening `Z ⟶ Z'`) and the affine morphism
`X_Z ⟶ X_Y` (Stacks 03WI), and `h0DL7` glues the two complexes, which are pseudo-coherent, to an
object of `D(𝒪_{X_{Y'}})`. It is `Y'`-perfect by `h0DL4`, `Y ⟶ Y'` being a finite order
thickening (`Stacks.Pushout.isFiniteOrderThickening_of_isPushout`); and its negative fibre
self-extensions vanish because condition (2) of Stacks 0DLD is a condition on points and every
field-valued point of `Y'` lifts to `Y`
(`AlgebraicGeometry.Space.exists_lift_of_isFieldObject`). Essential surjectivity of the
comparison is read off from these cocones by
`Deformation.Artin.essSurj_fiberSquareComparison_of_nonempty_cocone`. -/
theorem essSurj_complexesFiberSquareComparison (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
    (h0DL4 : ∀ {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left) →
      ∀ (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T)),
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (complexesFunctor D).IsFibered := hfib.isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).EssSurj := by
  let : (complexesFunctor D).IsFibered := hfib.isFibered
  refine Deformation.Artin.essSurj_fiberSquareComparison_of_nonempty_cocone hfib _ f i b a
    w.symm ?_
  rintro ⟨u, x, y, α, β, hα, hβ⟩
  obtain rfl : u.T.left = Z := IsHomLift.domain_eq (complexesFunctor D) f α
  obtain rfl : x.T.left = Y := IsHomLift.codomain_eq (complexesFunctor D) f α
  obtain rfl : y.T.left = Z' := IsHomLift.codomain_eq (complexesFunctor D) i β
  have hα' : (complexesFunctor D).IsHomLift (R := (complexesFunctor D).obj u)
      (S := (complexesFunctor D).obj x) f α := hα
  have hβ' : (complexesFunctor D).IsHomLift (R := (complexesFunctor D).obj u)
      (S := (complexesFunctor D).obj y) i β := hβ
  obtain rfl : f = α.base.left := IsHomLift.eq_of_isHomLift (p := complexesFunctor D) f α
  obtain rfl : i = β.base.left := IsHomLift.eq_of_isHomLift (p := complexesFunctor D) i β
  -- the base map `Y' ⟶ B`, by Stacks 07SY
  have hpushSp := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS
    β.base.left α.base.left a b hi.isThickening hpush
  let g' : schemeSpace Y' ⟶ D.Y := hpushSp.desc y.T.hom x.T.hom
    ((CostructuredArrow.w β.base).trans (CostructuredArrow.w α.base).symm)
  let T' : SchemesOver D.Y := CostructuredArrow.mk (Y := Y') (S := schemeSpaceFunctor B S hS) g'
  let ξb : x.T ⟶ T' := CostructuredArrow.homMk b (hpushSp.inr_desc _ _ _)
  let ηb : y.T ⟶ T' := CostructuredArrow.homMk a (hpushSp.inl_desc _ _ _)
  have hcommT : α.base ≫ ξb = β.base ≫ ηb := CostructuredArrow.hom_ext _ _ w.symm
  -- the pushout of base changes, by Stacks 07W3
  have hwSp : D.relativeMap α.base ≫ D.relativeMap ξb =
      D.relativeMap β.base ≫ D.relativeMap ηb := by
    rw [← baseChangeMap_comp, ← baseChangeMap_comp, hcommT]
  have hsq : IsPushout (D.relativeMap β.base) (D.relativeMap α.base) (D.relativeMap ηb)
      (D.relativeMap ξb) :=
    h07W3 β.base.left α.base.left a b hi.isThickening hf hpush (D.projection T')
      (D.projection x.T) (D.projection y.T) (D.projection u.T) (D.relativeMap ξb)
      (D.relativeMap ηb) (D.relativeMap α.base) (D.relativeMap β.base)
      (D.projection_isFlat T') (isPullback_baseChangeMap D.f ξb)
      (isPullback_baseChangeMap D.f ηb) (isPullback_baseChangeMap D.f α.base)
      (baseChangeMap_comp_inclusion D.f β.base) hwSp
  have hkth : IsThickeningHom B S hS (D.relativeMap β.base) :=
    isThickeningHom_of_isPullback B S hS (isPullback_baseChangeMap D.f β.base).flip
      (FormalSpace.isThickeningHom_yonedaSpace_map B S hS β.base.left hi.isThickening)
  have hlaff : IsAffineHom B S hS (D.relativeMap α.base).hom :=
    IsAffineHom.of_isPullback (isPullback_hom_of_isPullback_spaces
      (isPullback_baseChangeMap D.f α.base)).flip
      (isAffineHom_of_presheaf ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        @_root_.AlgebraicGeometry.IsAffineHom α.base.left).2 hf))
  -- the glued complex, by Stacks 0DL7
  obtain ⟨N, eQ, eP', hcompat⟩ := h0DL7 _ _ _ _ hsq hkth hlaff x.E y.E
    x.relativelyPerfect.1 y.relativelyPerfect.1 (asIso α.fibre ≪≫ (asIso β.fibre).symm)
  have hbfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map b) :=
    Stacks.Pushout.isFiniteOrderThickening_of_isPushout hi hpush
  -- `Y'`-perfectness, by Stacks 0DL4
  have hperf : D.IsRelativelyPerfect T' N := h0DL4 ξb hbfin N x.E eQ x.relativelyPerfect
  -- condition (2) of Stacks 0DLD, a condition on points
  have hext : D.HasNoNegativeFibreExt T' N := by
    intro T₀ hT₀ yy j hj
    obtain ⟨y', hy'⟩ := exists_lift_of_isFieldObject ξb hbfin hT₀ yy
    let e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap yy)).obj N ≅
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y')).obj x.E :=
      (D.relativeMapComparison hy'.symm).app N ≪≫ (D.compComparison y' ξb).app N ≪≫
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y')).mapIso eQ
    have := x.noNegativeFibreExt T₀ hT₀ y' j hj
    exact (e.homCongr ((shiftFunctor _ j).mapIso e)).subsingleton
  let z : ComplexesObject D := ⟨T', N, hperf, hext⟩
  let ξ : x ⟶ z := (⟨ξb, eQ.hom, inferInstance⟩ : ComplexesHom x z)
  let η : y ⟶ z := (⟨ηb, eP'.hom, inferInstance⟩ : ComplexesHom y z)
  refine ⟨⟨z, ξ, η, ?_, ?_, ?_⟩⟩
  · exact (inferInstance : (complexesFunctor D).IsHomLift ((complexesFunctor D).map ξ) ξ)
  · exact (inferInstance : (complexesFunctor D).IsHomLift ((complexesFunctor D).map η) η)
  · exact complexesHom_comp_eq_comp_of_compat α β ξ η hcommT hwSp hcompat

/-- **Stacks 0DLK, from the results it uses.** In Situation 0DLE, let `i ≫ a = f ≫ b` be a
commutative square of the site whose image in schemes is a pushout `Y' = Y ⨿_Z Z'` along the
finite order thickening `i : Z ⟶ Z'` and the affine morphism `f : Z ⟶ Y`. Then the functor on
fibre categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence, granted Stacks 0DLG (`h0DLG`, not yet proved here), which gives full
faithfulness, and Stacks 07W3, 0DL7 and 0DL4 (`h07W3`, `h0DL7`, `h0DL4`, not yet proved here), which
give essential surjectivity
(`AlgebraicGeometry.Space.ComplexesSituation.essSurj_complexesFiberSquareComparison`). -/
theorem isEquivalence_complexesFiberSquareComparison (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
    (h0DL4 : ∀ {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left) →
      ∀ (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T)),
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (complexesFunctor D).IsFibered := hfib.isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).IsEquivalence :=
  isEquivalence_complexesFiberSquareComparison_of_essSurj D hfib h0DLG i f a b w hi hpush
    (essSurj_complexesFiberSquareComparison D hfib h07W3 h0DL7 h0DL4 i f a b w hi hpush)

/-- **Condition (RS*) for `Complexes_{X/B}`, from the results Stacks 0DLK uses.** In Situation
0DLE, granted Stacks 0DLG, 07W3, 0DL7 and 0DL4 (each pending, see
`AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison`), the
category `Complexes_{X/B}` satisfies condition (RS*) of Stacks 07Y8. -/
theorem satisfiesRSStar_complexesFunctor (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
    (h0DL4 : ∀ {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left) →
      ∀ (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T)),
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E') :
    Deformation.Artin.SatisfiesRSStar B S hS (complexesFunctor D) hfib :=
  satisfiesRSStar_complexesFunctor_of_essSurj D hfib h0DLG fun i f a b w hi hf hpush =>
    have := hf
    essSurj_complexesFiberSquareComparison D hfib h07W3 h0DL7 h0DL4 i f a b w hi hpush

/-- **Condition (RS) for `Complexes_{X/B}`, from the results Stacks 0DLK uses**: the hypothesis
`h0DLK` of `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`, in
exactly that shape, granted Stacks 0DLG, 07W3, 0DL7 and 0DL4 (each pending, see
`AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison`). It is
condition (RS*)
(`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor`) followed by
Stacks 0CXN, observation (4) (`Deformation.Artin.satisfiesRS_of_satisfiesRSStar`). -/
theorem satisfiesRS_complexesFunctor (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib))
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
    (h0DL4 : ∀ {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left) →
      ∀ (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T)),
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E') :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D) hfib :=
  Deformation.Artin.satisfiesRS_of_satisfiesRSStar B S hS (complexesFunctor D) hfib
    (satisfiesRSStar_complexesFunctor D hfib h0DLG h07W3 h0DL7 h0DL4)

end AlgebraicGeometry.Space.ComplexesSituation

end
