module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackMorGlue
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCorner
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.FullyFaithfulDescentMorphisms

/-!
# Existence of a morphism of a fibre agreeing with a family of local morphisms

The four locality steps for the property

> there is a morphism between the chosen pullbacks of `x` and of `y` along `Y ⟶ U` which agrees
> with the family `ψ`

of an object `Y` of the slice at `U`, in the form
`AlgebraicGeometry.BigHOver.of_localOnGenerators` consumes them.

## Main results

* `AlgebraicGeometry.BigHOver.morAgree_of_fullyFaithful_toDescentData`: gluing a morphism
  agreeing with `ψ` along an h covering family along which descent of morphisms holds; the step
  for a flat proper surjection of finite presentation onto an affine object is this for the
  one-element family, by condition (2) of Stacks 0EX9 in its descent form.
* `AlgebraicGeometry.BigHOver.morAgree_zariski`: the Zariski step, which is the existence half of
  `CategoryTheory.Functor.existsUnique_fiberHom_of_isStackInGroupoids` for condition (1) of
  Stacks 0EX9.  The gluing isomorphisms it needs over the overlaps are supplied by
  `AlgebraicGeometry.BigHOver.MorAgree.eq`: the local solutions are unique, so they automatically
  agree over every overlap.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-- Base change of the forward direction of `CategoryTheory.Functor.pullbackFiberIdIso` along `b`
contracts the iterated chosen pullback, the companion of
`CategoryTheory.Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq` for the other direction. -/
public theorem pullbackFiberHom_pullbackFiberIdIso_hom_eq {T Z : BigHOver B S hS}
    (w : p.Fiber T) (b : Z ⟶ T) :
    Functor.pullbackFiberHom (Functor.pullbackFiberIdIso w).hom b =
      (Functor.pullbackFiberCompIso' w (𝟙 T) b b (Category.comp_id b)).hom := by
  have hkey : Functor.pullbackFiberHom (Functor.pullbackFiberIdIso w).hom b ≫
      (Functor.pullbackFiberCompIso' w (𝟙 T) b b (Category.comp_id b)).inv = 𝟙 _ := by
    rw [← Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq, ← Functor.pullbackFiberHom_comp,
      Iso.hom_inv_id, Functor.pullbackFiberHom_id]
  rw [Iso.comp_inv_eq, Category.id_comp] at hkey
  exact hkey

open Functor.IsFibered Functor.IsFibered.CartStruct in
/-- **The structural isomorphism of the comparison functor of a cartesian square is the comparison
of the two contractions.** At an object `w` of the fibre over the base, the comparison of the two
cartesian structures around the square is the contraction of the iterated chosen pullback along
`z` then `e`, followed by the inverse of the contraction along `b` then `d`.

Both contractions are compared with the chosen cartesian structure of the diagonal `n` of the
square, the first by `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_cartPullbackOfEq` and the
second by `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_cartPullbackOfEq_eq_of_fac` — whose
morphism is an argument, so that the two spellings of an iterated chosen pullback do not have to be
identified by instance search — and
`CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_trans` composes the two comparisons.  The
transport along the commutativity of the square is invisible to the projections by
`CategoryTheory.Functor.IsFibered.CartStruct.proj_cast`. -/
public theorem cmpMor_cartComp_cartCompOfSquare {X X' Z E : BigHOver B S hS}
    (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z) (hsq : IsPullback e d z b)
    {n : E ⟶ X} (hn : e ≫ z = n) (w : p.Fiber X) :
    cmpMor (cartComp z e) (cartCompOfSquare b d hsq) w =
      (Functor.pullbackFiberCompIso' w z e n hn).hom ≫
        (Functor.pullbackFiberCompIso' w b d n (hsq.w.symm.trans hn)).inv := by
  have hfst : cmpMor (cartComp z e) (cartPullbackOfEq hn) w =
      (Functor.pullbackFiberCompIso' w z e n hn).hom := cmpMor_cartPullbackOfEq hn w
  have hsnd : cmpMor (cartCompOfSquare b d hsq) (cartPullbackOfEq hn) w =
      (Functor.pullbackFiberCompIso' w b d n (hsq.w.symm.trans hn)).hom := by
    refine cmpMor_cartPullbackOfEq_eq_of_fac hn (cartCompOfSquare b d hsq) w _
      ((Functor.pullbackFiberCompIso'_hom_fac w b d n (hsq.w.symm.trans hn)).trans ?_)
    exact (proj_cast hsq.w (cartComp b d) w).symm
  have htr := cmpMor_trans (cartComp z e) (cartCompOfSquare b d hsq) (cartPullbackOfEq hn) w
  rw [hfst, hsnd] at htr
  exact Iso.eq_comp_inv _ |>.mpr htr

variable {U : BigHOver B S hS} {x y : p.Fiber U}
variable {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}
variable {ψ : ∀ i, Functor.pullbackFiber p x (f i) ⟶ Functor.pullbackFiber p y (f i)}

/-- **Gluing a morphism agreeing with `ψ` along a family with fully faithful descent.** A
morphism agreeing with `ψ` over each member of a family of an object `Y` of the slice at `U`
glues to one over `Y`, as soon as the family generates a covering sieve of the h topology and the
functor from the fibre over `Y` to the descent data relative to it is fully faithful. -/
public theorem morAgree_of_fullyFaithful_toDescentData
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Y : Over U} (E : PreZeroHypercover.{u + 1} Y)
    (hff : Nonempty ((Functor.IsFibered.pullbackPseudofunctor p).toDescentData
      (fun i ↦ (E.f i).left)).FullyFaithful)
    (hcov : Sieve.ofArrows (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left) ∈
      BigHOver.topology B S hS Y.left)
    (hloc : ∀ i, ∃ m : Functor.pullbackFiber p x (E.X i).hom ⟶
      Functor.pullbackFiber p y (E.X i).hom, MorAgree ψ (E.X i).hom m) :
    ∃ m : Functor.pullbackFiber p x Y.hom ⟶ Functor.pullbackFiber p y Y.hom,
      MorAgree ψ Y.hom m := by
  classical
  choose m hm using hloc
  have hw : ∀ i, (E.f i).left ≫ Y.hom = (E.X i).hom := fun i ↦ Over.w (E.f i)
  -- the local solutions, read between the iterated chosen pullbacks
  set κx : ∀ i, Functor.pullbackFiber p (Functor.pullbackFiber p x Y.hom) ((E.f i).left) ≅
      Functor.pullbackFiber p x ((E.X i).hom) :=
    fun i ↦ Functor.pullbackFiberCompIso' x Y.hom ((E.f i).left) ((E.X i).hom) (hw i) with hκx
  set κy : ∀ i, Functor.pullbackFiber p (Functor.pullbackFiber p y Y.hom) ((E.f i).left) ≅
      Functor.pullbackFiber p y ((E.X i).hom) :=
    fun i ↦ Functor.pullbackFiberCompIso' y Y.hom ((E.f i).left) ((E.X i).hom) (hw i) with hκy
  set ψ' : ∀ i, Functor.pullbackFiber p (Functor.pullbackFiber p x Y.hom) ((E.f i).left) ⟶
      Functor.pullbackFiber p (Functor.pullbackFiber p y Y.hom) ((E.f i).left) :=
    fun i ↦ (κx i).hom ≫ m i ≫ (κy i).inv with hψ'
  -- the compatibility over an overlap, from uniqueness of a morphism agreeing with `ψ`
  have hcompat : ∀ (i j : E.I₀) {Z : BigHOver B S hS} (ε : Z ⟶ (E.X i).left)
      (ε' : Z ⟶ (E.X j).left) (q : Z ⟶ Y.left) (hq₁ : ε ≫ (E.f i).left = q)
      (hq₂ : ε' ≫ (E.f j).left = q),
      Functor.baseChangeFiberMor (ψ' i) ε q hq₁ q hq₁ =
        Functor.baseChangeFiberMor (ψ' j) ε' q hq₂ q hq₂ := by
    intro i j Z ε ε' q hq₁ hq₂
    have hr : ε ≫ (E.X i).hom = q ≫ Y.hom := by rw [← hw i, ← Category.assoc, hq₁]
    have hr' : ε' ≫ (E.X j).hom = q ≫ Y.hom := by rw [← hw j, ← Category.assoc, hq₂]
    rw [hψ', Functor.baseChangeFiberMor_conj (hw i) (m i) hq₁ rfl hr,
      Functor.baseChangeFiberMor_conj (hw j) (m j) hq₂ rfl hr']
    congr 1
    refine congrArg (fun n ↦ n ≫ _) (MorAgree.eq (ψ := ψ) h1 h2 h3 h4 hf ?_ ?_)
    · exact (hm i).baseChange ε (q ≫ Y.hom) hr
    · exact (hm j).baseChange ε' (q ≫ Y.hom) hr'
  obtain ⟨M, hM, -⟩ := Functor.existsUnique_fiberHom_of_fullyFaithful_toDescentData
    (fun i ↦ (E.f i).left) hff ψ' hcompat
  refine ⟨M, morAgree_of_covering h1 h2 h3 h4 M (fun i ↦ (E.f i).left) (fun i ↦ (E.X i).hom) hw
    hcov fun i ↦ ?_⟩
  have hbc : Functor.baseChangeFiberMor M ((E.f i).left) ((E.X i).hom) (hw i) ((E.X i).hom)
      (hw i) = m i := by
    rw [Functor.baseChangeFiberMor, hM i]
    simp [hψ', hκx, hκy]
  rw [hbc]
  exact hm i

/-- **The Zariski step.** A morphism agreeing with `ψ` over each member of a Zariski covering
family of an object `Y` of the slice at `U` glues to one over `Y`.

Condition (1) of Stacks 0EX9 makes the functor from the fibre over `Y` to the descent data relative
to the family fully faithful,
`CategoryTheory.Functor.nonempty_fullyFaithful_toDescentData_of_isStackInGroupoids`, and the family
is an h covering by `AlgebraicGeometry.BigHOver.zariskiTopology_le_topology`, so this is
`AlgebraicGeometry.BigHOver.morAgree_of_fullyFaithful_toDescentData`. -/
public theorem morAgree_zariski
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Y : Over U} (E : PreZeroHypercover.{u + 1} Y)
    (hE : (E.map (sliceToScheme B S hS U)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((sliceToScheme B S hS U).obj Y))
    (hloc : ∀ i, ∃ m : Functor.pullbackFiber p x (E.X i).hom ⟶
      Functor.pullbackFiber p y (E.X i).hom, MorAgree ψ (E.X i).hom m) :
    ∃ m : Functor.pullbackFiber p x Y.hom ⟶ Functor.pullbackFiber p y Y.hom,
      MorAgree ψ Y.hom m := by
  have hcov : Sieve.ofArrows (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left) ∈
      zariskiTopology B S hS Y.left :=
    Precoverage.generate_mem_toGrothendieck
      ⟨⟨E.I₀, fun i ↦ (E.X i).left, fun i ↦ (E.f i).left⟩, rfl, hE⟩
  exact morAgree_of_fullyFaithful_toDescentData h1 h2 h3 h4 hf E
    (Functor.nonempty_fullyFaithful_toDescentData_of_isStackInGroupoids h1 _ hcov)
    (zariskiTopology_le_topology B S hS _ hcov) hloc

open Functor.IsFibered in
/-- **The amalgamation step.** Morphisms agreeing with `ψ` over the centre and over the
modification of a cartesian square along which the comparison functor is an equivalence come from
one over the base, which restricts to them. -/
public theorem exists_morAgree_square
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Xb Xm Xc Xe : BigHOver B S hS} (b : Xm ⟶ Xb) (z : Xc ⟶ Xb) (d : Xe ⟶ Xm) (e : Xe ⟶ Xc)
    (hsq : IsPullback e d z b)
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    {F : Xb ⟶ U} {Fz : Xc ⟶ U} (hFz : z ≫ F = Fz) {Fb : Xm ⟶ U} (hFb : b ≫ F = Fb)
    {mZ : Functor.pullbackFiber p x Fz ⟶ Functor.pullbackFiber p y Fz} (hmZ : MorAgree ψ Fz mZ)
    {mX : Functor.pullbackFiber p x Fb ⟶ Functor.pullbackFiber p y Fb} (hmX : MorAgree ψ Fb mX) :
    ∃ M : Functor.pullbackFiber p x F ⟶ Functor.pullbackFiber p y F,
      Functor.baseChangeFiberMor M z Fz hFz Fz hFz = mZ ∧
      Functor.baseChangeFiberMor M b Fb hFb Fb hFb = mX := by
  set x' := Functor.pullbackFiber p x F with hx'
  set y' := Functor.pullbackFiber p y F with hy'
  set κxz := Functor.pullbackFiberCompIso' x F z Fz hFz with hκxz
  set κyz := Functor.pullbackFiberCompIso' y F z Fz hFz with hκyz
  set κxb := Functor.pullbackFiberCompIso' x F b Fb hFb with hκxb
  set κyb := Functor.pullbackFiberCompIso' y F b Fb hFb with hκyb
  set a : Functor.pullbackFiber p x' z ⟶ Functor.pullbackFiber p y' z :=
    κxz.hom ≫ mZ ≫ κyz.inv with ha
  set c : Functor.pullbackFiber p x' b ⟶ Functor.pullbackFiber p y' b :=
    κxb.hom ≫ mX ≫ κyb.inv with hc
  have hdb : d ≫ b = e ≫ z := hsq.w.symm
  have hrz : (e ≫ z) ≫ F = e ≫ Fz := by rw [Category.assoc, hFz]
  have hrb : d ≫ Fb = e ≫ Fz := by rw [← hFb, ← Category.assoc, hdb, Category.assoc, hFz]
  -- the structural isomorphism of the comparison functor, as a comparison of two contractions
  have hiso : ∀ w : p.Fiber Xb,
      ((twoFibreProductComparison B S hS p b z d e hsq).obj w).iso.hom =
        (Functor.pullbackFiberCompIso' w z e (e ≫ z) rfl).hom ≫
          (Functor.pullbackFiberCompIso' w b d (e ≫ z) hdb).inv := fun w ↦ by
    rw [twoFibreProductComparison_obj_iso_hom]
    exact cmpMor_cartComp_cartCompOfSquare b z d e hsq rfl w
  -- the agreement over the exceptional corner, from uniqueness of a morphism agreeing with `ψ`
  have hkey : Functor.baseChangeFiberMor a e (e ≫ z) rfl (e ≫ z) rfl =
      Functor.baseChangeFiberMor c d (e ≫ z) hdb (e ≫ z) hdb := by
    rw [ha, hc, hκxz, hκyz, hκxb, hκyb,
      Functor.baseChangeFiberMor_conj hFz mZ rfl hrz rfl,
      Functor.baseChangeFiberMor_conj hFb mX hdb hrz hrb]
    exact congrArg (fun m ↦ _ ≫ m ≫ _)
      (MorAgree.eq (ψ := ψ) h1 h2 h3 h4 hf (hmZ.baseChange e (e ≫ Fz) rfl)
        (hmX.baseChange d (e ≫ Fz) hrb))
  rw [Functor.baseChangeFiberMor, Functor.baseChangeFiberMor, Iso.inv_comp_eq] at hkey
  -- the two sides of the agreement condition, with the iterated chosen pullbacks spelled as
  -- chosen pullbacks rather than as values of a composite of pullback functors
  set α : Functor.pullbackFiber p (Functor.pullbackFiber p x' z) e ⟶
      Functor.pullbackFiber p (Functor.pullbackFiber p y' z) e :=
    Functor.pullbackFiberHom a e with hα
  set δ : Functor.pullbackFiber p (Functor.pullbackFiber p x' b) d ⟶
      Functor.pullbackFiber p (Functor.pullbackFiber p y' b) d :=
    Functor.pullbackFiberHom c d with hδ
  have wgoal : α ≫ ((twoFibreProductComparison B S hS p b z d e hsq).obj y').iso.hom =
      ((twoFibreProductComparison B S hS p b z d e hsq).obj x').iso.hom ≫ δ := by
    rw [hiso, hiso]
    exact (Category.assoc α (Functor.pullbackFiberCompIso' y' z e (e ≫ z) rfl).hom
        (Functor.pullbackFiberCompIso' y' b d (e ≫ z) hdb).inv).symm.trans
      ((congrArg (· ≫ (Functor.pullbackFiberCompIso' y' b d (e ≫ z) hdb).inv) hkey).trans (by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        exact (Category.assoc _ _ _).symm))
  rw [hα, Functor.fiberPullback_map_eq_pullbackFiberHom (p := p) e a |>.symm] at wgoal
  rw [hδ, Functor.fiberPullback_map_eq_pullbackFiberHom (p := p) d c |>.symm] at wgoal
  obtain ⟨M, hMz, hMb⟩ := exists_fiberHom b z d e hsq heq a c wgoal
  refine ⟨M, ?_, ?_⟩ <;>
  · rw [Functor.baseChangeFiberMor, ← Functor.fiberPullback_map_eq_pullbackFiberHom]
    simp [hMz, hMb, ha, hc, hκxz, hκyz, hκxb, hκyb]

end BigHOver

end AlgebraicGeometry

end
