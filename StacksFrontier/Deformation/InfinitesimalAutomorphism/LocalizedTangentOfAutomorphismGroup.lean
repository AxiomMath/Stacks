module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensional
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentAtPoint
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Difference

/-!
# Finite dimensionality of `Inf` from the infinitesimal automorphism group

Let `p : 𝓕 ⥤ 𝒞_Λ` be a predeformation category satisfying (RS), and let `y` be a point of `𝓕`
over the residue field. The library carries two descriptions of the infinitesimal automorphisms
of `𝓕` at `y` with their `k`-vector space structure:

* the tangent space `T_{id_y} Aut(y)` of the automorphism functor at the identity
  (`Deformation.localizedAutomorphismFunctorTangent`), with the natural structure of Stacks 06JX,
  whose addition is composition and whose scalar multiplication is transport along `ε ↦ cε`
  (`Deformation.localizedTangentEquivAut_add`, `Deformation.localizedTangentEquivAut_smul`);
* the group of infinitesimal automorphisms of a pushforward along a dual-number pair
  (`Deformation.infinitesimalAutomorphismGroup`, Stacks 06JS), with any vector space structure
  whose addition is composition and in which `c` acts by pushforward along a rescaling `ε ↦ cε`
  of a dual-number coordinate, as in Stacks 0E42.

This file shows that the second being finite dimensional forces the first to be: both are the
automorphism group of the chosen pushforward of `y` to the dual numbers, and the two scalar
actions are pushforwards along the same arrow.

## Main results

* `Deformation.ChosenPushforwardsAt.transportAut_eq_pushforwardAutomorphismHom`: transport along
  the arrow between two chosen pushforwards is pushforward along that arrow.
* `finiteDimensional_localizedAutomorphismFunctorTangent_of_infinitesimalAutomorphismGroup`:
  finite dimensionality of `Inf` from that of the infinitesimal automorphism group.

## References

* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ u₂ v₂

namespace Deformation

namespace ChosenPushforwardsAt

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C} {x : F}
  (P : ChosenPushforwardsAt p x) (hp : IsCofiberedInGroupoids p)

/-- **Transport along the arrow between two chosen pushforwards is pushforward along it.** -/
theorem transportAut_eq_pushforwardAutomorphismHom {A B : Under (p.obj x)} (f : A ⟶ B)
    (a : Aut (P.obj A)) :
    P.transportAut f a = pushforwardAutomorphismHom hp f.right (P.map f) (P.map_isHomLift f) a := by
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  change P.transportHom f a = pushforwardEndomorphism hp f.right (P.map f) (P.map_isHomLift f) a
  have := P.map_cocartesian f
  have := P.transportHom_isHomLift f a
  have := pushforwardEndomorphism_isHomLift hp f.right (P.map f) (P.map_isHomLift f) a
  apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
  rw [P.map_transportHom, hom_comp_eq_comp_pushforwardEndomorphism]

end ChosenPushforwardsAt

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k} (y : p.Fiber (residueFieldObject.{u, u, u} Λ k))

variable (Λ k) in
/-- The dual numbers over `k`, as the square-zero extension of `k` by the rank-one vector space. -/
def dualNumberToRankOne :
    DualNumber k →ₐ[Λ] ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) where
  toFun x := ⟨TrivSqZeroExt.fst x, TrivSqZeroExt.snd x⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change TrivSqZeroExt.fst x * TrivSqZeroExt.snd y + TrivSqZeroExt.snd x * TrivSqZeroExt.fst y =
        TrivSqZeroExt.fst x * TrivSqZeroExt.snd y + TrivSqZeroExt.fst y * TrivSqZeroExt.snd x
      ring
  commutes' _ := rfl

variable (Λ k) in
/-- The comparison of the dual numbers with the square-zero extension by the rank-one space is
bijective. -/
theorem dualNumberToRankOne_bijective : Function.Bijective (dualNumberToRankOne Λ k) :=
  ⟨fun _ _ h => TrivSqZeroExt.ext (congrArg TrivSqZeroExt.fst h) (congrArg TrivSqZeroExt.snd h),
    fun z => ⟨⟨TrivSqZeroExt.fst z, TrivSqZeroExt.snd z⟩, rfl⟩⟩

variable (Λ k) in
/-- The square-zero extension of `k` by the rank-one vector space is the dual numbers. -/
def rankOneDualNumberEquiv :
    ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) ≃ₐ[Λ] DualNumber k :=
  (AlgEquiv.ofBijective _ (dualNumberToRankOne_bijective Λ k)).symm

/-- The inverse of `rankOneDualNumberEquiv` keeps both components. -/
theorem rankOneDualNumberEquiv_symm_apply (x : DualNumber k) :
    (rankOneDualNumberEquiv Λ k).symm x = ⟨TrivSqZeroExt.fst x, TrivSqZeroExt.snd x⟩ :=
  rfl

/-- `rankOneDualNumberEquiv` preserves the second component. -/
theorem snd_rankOneDualNumberEquiv
    (z : ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))) :
    TrivSqZeroExt.snd (rankOneDualNumberEquiv Λ k z) = TrivSqZeroExt.snd z := by
  conv_rhs => rw [← (rankOneDualNumberEquiv Λ k).symm_apply_apply z]
  rfl

/-- `rankOneDualNumberEquiv` preserves the first component. -/
theorem fst_rankOneDualNumberEquiv
    (z : ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))) :
    TrivSqZeroExt.fst (rankOneDualNumberEquiv Λ k z) = TrivSqZeroExt.fst z := by
  conv_rhs => rw [← (rankOneDualNumberEquiv Λ k).symm_apply_apply z]
  rfl

/-- The dual-number coordinate of the canonical dual numbers under the base of a point. -/
def dualNumbersUnderAlgEquiv :
    (dualNumbersUnder (p := p) (x := y.1)).right ≃ₐ[Λ] DualNumber k :=
  (AlgEquiv.ofBijective (dualNumbersUnderHom (p := p) (x := y.1)).hom
    (dualNumbersUnderHom_bijective (p := p) (x := y.1))).trans (rankOneDualNumberEquiv Λ k)

/-- `dualNumbersUnderAlgEquiv` is `dualNumbersUnderHom` followed by `rankOneDualNumberEquiv`. -/
theorem dualNumbersUnderAlgEquiv_apply (a : (dualNumbersUnder (p := p) (x := y.1)).right) :
    dualNumbersUnderAlgEquiv y a =
      rankOneDualNumberEquiv Λ k ((dualNumbersUnderHom (p := p) (x := y.1)).hom a) :=
  rfl

/-- The first component of `dualNumbersUnderAlgEquiv` is the residue map. -/
private theorem fst_dualNumbersUnderAlgEquiv (a : (dualNumbersUnder (p := p) (x := y.1)).right) :
    TrivSqZeroExt.fst (dualNumbersUnderAlgEquiv y a) =
      (dualNumbersUnder (p := p) (x := y.1)).right.residueEquiv (IsLocalRing.residue _ a) :=
  (fst_rankOneDualNumberEquiv _).trans ((dualNumbersUnderHom (p := p) (x := y.1)).residue_comm a)

/-- The inverse of `dualNumbersUnderAlgEquiv`, unfolded. -/
theorem dualNumbersUnderAlgEquiv_symm_apply (w : DualNumber k) :
    (dualNumbersUnderAlgEquiv y).symm w =
      (AlgEquiv.ofBijective (dualNumbersUnderHom (p := p) (x := y.1)).hom
        (dualNumbersUnderHom_bijective (p := p) (x := y.1))).symm
          ((rankOneDualNumberEquiv Λ k).symm w) :=
  rfl

/-- The residue field is terminal in `𝒞_Λ`. -/
def isTerminalResidueFieldObject : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
  ArtinianLocalAlgCat.isTerminal_of_algEquiv _ (ULift.algEquiv (R := Λ) (A := k))

/-- The square-zero extension of `k` by the zero module is terminal in `𝒞_Λ`. -/
def isTerminalSquareZeroPUnit :
    IsTerminal ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k PUnit.{u + 1})) :=
  ArtinianLocalAlgCat.isTerminal_of_algEquiv _ (AlgEquiv.ofBijective
    (TrivSqZeroExt.fstHom Λ k PUnit.{u + 1})
    ⟨fun _ _ h => TrivSqZeroExt.ext h rfl,
      fun r => ⟨TrivSqZeroExt.inl r, rfl⟩⟩)

/-- The inclusion of the residue field into the canonical dual numbers under the base of `y`. -/
abbrev dualNumbersUnderInclusion :
    residueFieldObject.{u, u, u} Λ k ⟶ (dualNumbersUnder (p := p) (x := y.1)).right :=
  eqToHom y.2.symm ≫ (dualNumbersUnder (p := p) (x := y.1)).hom

/-- The reduction of the canonical dual numbers under the base of `y` to the residue field. -/
abbrev dualNumbersUnderReduction :
    (dualNumbersUnder (p := p) (x := y.1)).right ⟶ residueFieldObject.{u, u, u} Λ k :=
  isTerminalResidueFieldObject.from _

/-- The inclusion of the residue field into the canonical dual numbers under the base of `y` and
the reduction back form a canonical dual-number pair. -/
theorem isCanonicalDualNumberPair_dualNumbersUnder :
    IsCanonicalDualNumberPair (dualNumbersUnderInclusion y) (dualNumbersUnderReduction y) := by
  refine ⟨ULift.algEquiv (R := Λ) (A := k), dualNumbersUnderAlgEquiv y, ?_, ?_,
    isTerminalResidueFieldObject.hom_ext _ _⟩
  · let m : p.obj y.1 ⟶
        (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k PUnit.{u + 1}) :=
      isTerminalSquareZeroPUnit.from _
    refine AlgHom.ext fun t => ?_
    change rankOneDualNumberEquiv Λ k ((dualNumbersUnderHom (p := p) (x := y.1)).hom
      ((dualNumbersUnder (p := p) (x := y.1)).hom.hom ((eqToHom y.2.symm).hom t))) = _
    rw [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
      dualNumbersUnder_hom_comp_dualNumbersUnderHom (p := p) (x := y.1) m]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_rankOneDualNumberEquiv]
      exact ((eqToHom y.2.symm ≫ m ≫ (artinianSquareZeroExtensionFunctor Λ k).map
        (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k)).residue_comm t).trans
        (Examples.residueFieldObject_residueEquiv_residue t)
    · rw [snd_rankOneDualNumberEquiv]
      exact squareZeroExtensionArtinian_map_snd (Λ := Λ)
        (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k) _
  · refine AlgHom.ext fun a => ?_
    exact ((Examples.residueFieldObject_residueEquiv_residue _).symm.trans
      ((dualNumbersUnderReduction y).residue_comm a)).trans
      (fst_dualNumbersUnderAlgEquiv y a).symm

/-- Under `rankOneDualNumberEquiv`, the map induced by multiplication by `c` on the rank-one space
is the rescaling `ε ↦ cε` of the dual numbers. -/
theorem rankOneDualNumberEquiv_map_smul (c : k) (w : DualNumber k) :
    rankOneDualNumberEquiv Λ k (((artinianSquareZeroExtensionFunctor Λ k).map
      (c • 𝟙 (FGModuleCat.of k k))).hom ((rankOneDualNumberEquiv Λ k).symm w)) =
        TrivSqZeroExt.map (c • LinearMap.id) w := by
  apply TrivSqZeroExt.ext
  · rw [fst_rankOneDualNumberEquiv, TrivSqZeroExt.fst_map]
    exact ((artinianSquareZeroExtensionFunctor Λ k).map (c • 𝟙 (FGModuleCat.of k k))).residue_comm _
  · rw [snd_rankOneDualNumberEquiv, TrivSqZeroExt.snd_map]
    refine (squareZeroExtensionArtinian_map_snd (Λ := Λ) (c • 𝟙 (FGModuleCat.of k k)) _).trans ?_
    rfl

/-- The rescaling `ε ↦ cε` of the canonical dual numbers is a rescaling of a dual-number
coordinate. -/
theorem isDualNumberScaling_tangentScaling (c : k) :
    Examples.IsDualNumberScaling c (tangentScaling (p := p) (x := y.1) c).right := by
  have key : ∀ w : DualNumber k, dualNumbersUnderAlgEquiv y
      ((tangentScaling (p := p) (x := y.1) c).right.hom ((dualNumbersUnderAlgEquiv y).symm w)) =
        TrivSqZeroExt.map (c • LinearMap.id) w := by
    intro w
    rw [dualNumbersUnderAlgEquiv_apply, ← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
      tangentScaling_right_comp_dualNumbersUnderHom (p := p) (x := y.1) c,
      ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, dualNumbersUnderAlgEquiv_symm_apply,
      AlgEquiv.ofBijective_apply_symm_apply, rankOneDualNumberEquiv_map_smul]
  refine ⟨dualNumbersUnderAlgEquiv y, fun t => ?_, fun t => ?_, ?_⟩
  · exact fst_dualNumbersUnderAlgEquiv y t
  · rw [key, TrivSqZeroExt.map_inl]
  · rw [key]
    change TrivSqZeroExt.map (c • LinearMap.id) (TrivSqZeroExt.inr 1) = c • TrivSqZeroExt.inr 1
    rw [TrivSqZeroExt.map_inr, ← TrivSqZeroExt.inr_smul]
    rfl

/-- **Finite dimensionality of the infinitesimal automorphisms from the infinitesimal
automorphism group.** Let `p` be a predeformation category satisfying (RS) and `y` a point over
the residue field. Suppose that at every pushforward `i : y ⟶ xε` along a dual-number pair the
group of infinitesimal automorphisms carries a finite-dimensional `k`-vector space structure whose
addition is composition and in which `c` acts by pushforward along every rescaling `ε ↦ cε` of a
dual-number coordinate fixing `i`. Then the tangent space at the identity of the automorphism
functor of `y`, with its natural structure of Stacks 06JX, is finite dimensional. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_infinitesimalAutomorphismGroup
    (hp : IsPredeformationCategory p) (hRS : SatisfiesRS p) (Q : ChosenPushforwardsAt p y.1)
    (hInf : ∀ {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k} {xε : p.Fiber Aε}
      (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
      (hpair : IsCanonicalDualNumberPair g e) (i : y.1 ⟶ xε.1) (hi : p.IsHomLift g i),
      ∃ hA : AddCommGroup (infinitesimalAutomorphismGroup hp g e hpair i hi),
        letI := hA
        ∃ hM : Module k (infinitesimalAutomorphismGroup hp g e hpair i hi),
          letI := hM
          (∀ a b : infinitesimalAutomorphismGroup hp g e hpair i hi, a + b = a * b) ∧
          (∀ (c : k) (s : Aε ⟶ Aε), Examples.IsDualNumberScaling c s → s ≫ e = e →
            ∀ (j : xε.1 ⟶ xε.1) (hj : p.IsHomLift s j), i ≫ j = i →
              ∀ a : infinitesimalAutomorphismGroup hp g e hpair i hi,
                ∃ b : infinitesimalAutomorphismGroup hp g e hpair i hi,
                  b.val = pushforwardAutomorphismHom hp.cofibered s j hj a.val ∧ c • a = b) ∧
          FiniteDimensional k (infinitesimalAutomorphismGroup hp g e hpair i hi)) :
    letI := naturalLocalizedTangentAddCommGroup Q hRS
    letI := naturalLocalizedTangentModule Q hRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent Q) := by
  let := naturalLocalizedTangentAddCommGroup Q hRS
  let := naturalLocalizedTangentModule Q hRS
  let D := dualNumbersUnder (p := p) (x := y.1)
  have hi : p.IsHomLift (dualNumbersUnderInclusion y) (Q.inclusion D) := by
    have := Q.inclusion_cocartesian D
    infer_instance
  obtain ⟨hA, hM, hadd, hsmul, hfin⟩ := hInf (xε := Q.obj D) (dualNumbersUnderInclusion y)
    (dualNumbersUnderReduction y) (isCanonicalDualNumberPair_dualNumbersUnder y) (Q.inclusion D) hi
  let K := localizedTangentEquivAut Q hp
  have hmem : ∀ a, K a ∈ infinitesimalAutomorphisms hp.cofibered (dualNumbersUnderInclusion y)
      (dualNumbersUnderReduction y) (isCanonicalDualNumberPair_dualNumbersUnder y)
      (Q.inclusion D) hi := fun a => by
    rw [infinitesimalAutomorphisms_eq_top hp y (Q.obj D)]
    trivial
  let Φ : localizedAutomorphismFunctorTangent Q →ₗ[k] infinitesimalAutomorphismGroup hp
      (dualNumbersUnderInclusion y) (dualNumbersUnderReduction y)
      (isCanonicalDualNumberPair_dualNumbersUnder y) (Q.inclusion D) hi :=
    { toFun := fun a => ⟨K a, hmem a⟩
      map_add' := fun a b => by
        rw [hadd]
        exact Subtype.ext (localizedTangentEquivAut_add Q hp hRS a b)
      map_smul' := fun c a => by
        obtain ⟨b, hb, hcb⟩ := hsmul c (tangentScaling (p := p) (x := y.1) c).right
          (isDualNumberScaling_tangentScaling y c) (isTerminalResidueFieldObject.hom_ext _ _)
          (Q.map (tangentScaling (p := p) (x := y.1) c)) (Q.map_isHomLift _) (Q.inclusion_map _)
          ⟨K a, hmem a⟩
        rw [RingHom.id_apply, hcb]
        exact Subtype.ext ((localizedTangentEquivAut_smul Q hp hRS c a).trans
          ((Q.transportAut_eq_pushforwardAutomorphismHom hp.cofibered _ _).trans hb.symm)) }
  exact FiniteDimensional.of_injective Φ fun a b h => K.injective (congrArg Subtype.val h :)

end Deformation

end
