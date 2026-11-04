module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel
import all StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel

/-!
# A strict monomorphism into a filtered injective object

Filtered objects with a single jump, biproducts of filtered objects, and the construction of
[Stacks, Tag 05TS]: a finitely filtered object embeds by a strict monomorphism into a finite direct
sum of filtered objects with a single jump at an injective object.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveResolutionDegreeZero

namespace CochainComplex.FilteredInjective.Resolution

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

section Building

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

omit [Abelian 𝒜] in
/-- A commuting square whose left-hand leg is an isomorphism and whose opposite leg is a
monomorphism is a pullback square. In the situation of `IsStrictHom` this is strictness at an
index `p` where the filtration of the source is already exhausted. -/
private lemma isPullback_of_isIso_of_mono {P X Y Z : 𝒜} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
    (g : Y ⟶ Z) (w : fst ≫ f = snd ≫ g) [IsIso snd] [Mono f] : IsPullback fst snd f g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s => s.snd ≫ inv snd)
    (fun s => ?_) (fun _ => by simp) (fun _ _ _ h₂ => by simp [← h₂]))
  rw [← cancel_mono f, Category.assoc, w]
  simp [s.condition]

/-- A commuting square with zero objects in the two corners of one leg and a monomorphism in the
opposite corner is a pullback square: it exhibits the vanishing kernel of that monomorphism. In
the situation of `IsStrictHom` this is strictness at an index `p` where both filtrations have
already vanished. -/
private lemma isPullback_of_isZero {P X Y Z : 𝒜} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
    (g : Y ⟶ Z) [Mono g] (hP : IsZero P) (hX : IsZero X) : IsPullback fst snd f g := by
  have w : fst ≫ f = snd ≫ g := by
    rw [hP.eq_of_src fst 0, hP.eq_of_src snd 0, zero_comp, zero_comp]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun _ => 0)
    (fun _ => hX.eq_of_tgt _ _) (fun s => ?_) (fun _ _ _ _ => hP.eq_of_tgt _ _))
  rw [zero_comp, ← cancel_mono g, zero_comp, ← s.condition, hX.eq_of_tgt s.fst 0, zero_comp]

private lemma isZero_cokernel_of_isIso {X Y : 𝒜} (f : X ⟶ Y) [IsIso f] : IsZero (cokernel f) := by
  have h : cokernel.π f = 0 := by rw [← cancel_epi f, cokernel.condition, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π f)]
  simp [h]

private lemma injective_cokernel_of_isZero {X Y : 𝒜} (f : X ⟶ Y) (h : IsZero X) [Injective Y] :
    Injective (cokernel f) := by
  have : IsIso (cokernel.π f) := by rw [h.eq_of_src f 0]; infer_instance
  exact Injective.of_iso (asIso (cokernel.π f)) inferInstance

/-- The biproduct of two isomorphisms is an isomorphism. -/
lemma isIso_biprod_map {X Y Z W : 𝒜} (f : X ⟶ Y) (g : Z ⟶ W) [IsIso f] [IsIso g] :
    IsIso (biprod.map f g) :=
  ⟨⟨biprod.map (inv f) (inv g), by apply biprod.hom_ext' <;> simp,
    by apply biprod.hom_ext' <;> simp⟩⟩

/-- The biproduct of two zero objects is a zero object. -/
lemma isZero_biprod {X Y : 𝒜} (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) := by
  rw [IsZero.iff_id_eq_zero]
  exact biprod.hom_ext _ _ (hX.eq_of_tgt _ _) (hY.eq_of_tgt _ _)

/-- The cokernel of a biproduct of two morphisms is the biproduct of their cokernels. -/
private noncomputable def cokernelBiprodMapIso {X Y Z W : 𝒜} (f : X ⟶ Y) (g : Z ⟶ W) :
    cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π g))
    (by apply biprod.hom_ext' <;> simp)
  inv := biprod.desc
    (cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← Category.assoc, show f ≫ biprod.inl = biprod.inl ≫ biprod.map f g by simp,
        Category.assoc, cokernel.condition, comp_zero]))
    (cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← Category.assoc, show g ≫ biprod.inr = biprod.inr ≫ biprod.map f g by simp,
        Category.assoc, cokernel.condition, comp_zero]))
  hom_inv_id := by
    apply coequalizer.hom_ext
    apply biprod.hom_ext' <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply coequalizer.hom_ext; simp
    · apply coequalizer.hom_ext; simp

/-! ### Graded pieces from the two neighbouring filtration steps -/

/-- A graded piece is injective as soon as the `p`-th filtration step is and the `(p + 1)`-st
vanishes: the graded piece is then the `p`-th step itself. -/
private lemma injective_gradedPiece_of_isZero {K : FilteredObject 𝒜 ℤᵒᵖ} {p : ℤ}
    (h : IsZero (K.filtration.obj (op (p + 1)))) [Injective (K.filtration.obj (op p))] :
    Injective ((gr p).obj K) :=
  injective_cokernel_of_isZero _ h

/-! ### Filtered objects with a single jump -/

/-- The endomorphism of `X` which is `0` at indices `≤ c` and the identity above `c`. Its kernels
are the steps of the filtration of `oneStepObj X c`; realising the steps as kernels of a single
family of endomorphisms of `X` keeps the underlying objects uniform in `p`, so that a morphism
into `oneStepObj X c` is a family of `kernel.lift`s with no transport along `p ≤ c`. -/
private noncomputable def stepArrow (X : 𝒜) (c p : ℤ) : X ⟶ X := if p ≤ c then 0 else 𝟙 X

@[local simp]
private lemma stepArrow_of_le {X : 𝒜} {c p : ℤ} (h : p ≤ c) : stepArrow X c p = 0 := by
  simp [stepArrow, h]

@[local simp]
private lemma stepArrow_of_not_le {X : 𝒜} {c p : ℤ} (h : ¬ p ≤ c) : stepArrow X c p = 𝟙 X := by
  simp [stepArrow, h]

private lemma isZero_kernel_stepArrow {X : 𝒜} {c p : ℤ} (h : ¬ p ≤ c) :
    IsZero (kernel (stepArrow X c p)) := by
  rw [stepArrow_of_not_le h]; exact isZero_kernel_of_mono (𝟙 X)

private lemma isIso_kernel_ι_stepArrow {X : 𝒜} {c p : ℤ} (h : p ≤ c) :
    IsIso (kernel.ι (stepArrow X c p)) := by
  rw [stepArrow_of_le h]; exact kernel.ι_zero_isIso

/-- A morphism into `X` composes to zero with `stepArrow X c p` as soon as it vanishes when
`p > c`: below the jump the arrow itself is zero, above it the morphism is. -/
private lemma comp_stepArrow_eq_zero {X T : 𝒜} {c p : ℤ} (φ : T ⟶ X)
    (h : ¬ p ≤ c → φ = 0) : φ ≫ stepArrow X c p = 0 := by
  by_cases hp : p ≤ c
  · rw [stepArrow_of_le hp, comp_zero]
  · rw [h hp, zero_comp]

/-- The filtered object `X` filtered with a single jump at `c`: `F^p X = X` for `p ≤ c` and
`F^p X = 0` for `p > c`. Its graded pieces are `gr^c = X` and `gr^p = 0` for `p ≠ c`, so it is a
filtered injective object exactly when `X` is an injective object of `𝒜`. -/
private noncomputable def oneStepObj (X : 𝒜) (c : ℤ) : FilteredObject 𝒜 ℤᵒᵖ where
  X := X
  filtration := filtrationOfSteps (fun p => MonoOver.mk (kernel.ι (stepArrow X c p)))
    (fun _ _ hqp => nonempty_hom_of_steps
      (fun p => MonoOver.mk (kernel.ι (stepArrow X c p)))
      (fun r => ⟨MonoOver.homMk
      (kernel.lift (stepArrow X c r) (kernel.ι (stepArrow X c (r + 1)))
        (comp_stepArrow_eq_zero _ (fun hr => (isZero_kernel_stepArrow
          (fun hc => hr (le_trans (Int.le_add_one le_rfl) hc))).eq_of_src _ _)))
      (kernel.lift_ι ..)⟩) hqp)

private lemma oneStepObj_ι_app (X : 𝒜) (c p : ℤ) :
    (oneStepObj X c).filtration.ι.app (op p) = kernel.ι (stepArrow X c p) := rfl

private lemma isIso_oneStepObj_ι_app {X : 𝒜} {c p : ℤ} (h : p ≤ c) :
    IsIso ((oneStepObj X c).filtration.ι.app (op p)) := isIso_kernel_ι_stepArrow h

private lemma isZero_oneStepObj_obj {X : 𝒜} {c p : ℤ} (h : ¬ p ≤ c) :
    IsZero ((oneStepObj X c).filtration.obj (op p)) := isZero_kernel_stepArrow h

private lemma injective_gradedPiece_oneStepObj (X : 𝒜) [Injective X] (c p : ℤ) :
    Injective ((gr p).obj (oneStepObj X c)) := by
  by_cases h : p ≤ c
  · by_cases h' : p + 1 ≤ c
    · exact (isZero_gr_obj_of_isIso_ι_app _ le_rfl (isIso_oneStepObj_ι_app h')).injective
    · have e : (oneStepObj X c).filtration.obj (op p) ≅ X :=
        @asIso _ _ _ _ ((oneStepObj X c).filtration.ι.app (op p))
          (isIso_oneStepObj_ι_app h)
      have : Injective ((oneStepObj X c).filtration.obj (op p)) :=
        Injective.of_iso e.symm inferInstance
      exact injective_gradedPiece_of_isZero (isZero_oneStepObj_obj h')
  · exact (isZero_gr_obj_of_isZero _ le_rfl (isZero_oneStepObj_obj h)).injective

/-- A morphism `φ : A.X ⟶ Y` which kills `F^p A` for every `p > c`, read as a morphism of
filtered objects `A ⟶ oneStepObj Y c`: the components are the `kernel.lift`s of the composites
`F^p A ⟶ A ⟶ Y`, and their compatibility with the inclusions is `kernel.lift_ι`.

The hypothesis is exactly what makes `φ` filtered, and it is weaker than the vanishing of
`F^p A` above `c`: for `φ` the composite `A ⟶ A / F^{c + 1} A ⟶ Y` it holds by construction. -/
private noncomputable def oneStepHomMk {A : FilteredObject 𝒜 ℤᵒᵖ} {Y : 𝒜} {c : ℤ} (φ : A.X ⟶ Y)
    (hA : ∀ p : ℤ, ¬ p ≤ c → A.filtration.ι.app (op p) ≫ φ = 0) : A ⟶ oneStepObj Y c :=
  FilteredObject.homMk φ
    (fun i => kernel.lift (stepArrow Y c i.unop) (A.filtration.ι.app i ≫ φ)
      (comp_stepArrow_eq_zero _ (fun h => hA i.unop h)))
    (fun _ => kernel.lift_ι ..)

@[local simp]
private lemma oneStepHomMk_hom {A : FilteredObject 𝒜 ℤᵒᵖ} {Y : 𝒜} {c : ℤ} (φ : A.X ⟶ Y)
    (hA : ∀ p : ℤ, ¬ p ≤ c → A.filtration.ι.app (op p) ≫ φ = 0) :
    (oneStepHomMk φ hA).hom = φ := rfl

/-- The filtered object with a single jump at an injective object `X` has `F^c = X`, vanishing steps
above `c`, and injective graded pieces. -/
private lemma oneStepObj_spec (X : 𝒜) [Injective X] (c : ℤ) :
    IsIso ((oneStepObj X c).filtration.ι.app (op c)) ∧
      (∀ p : ℤ, c + 1 ≤ p → IsZero ((oneStepObj X c).filtration.obj (op p))) ∧
      ∀ p : ℤ, Injective ((gr p).obj (oneStepObj X c)) :=
  ⟨isIso_oneStepObj_ι_app le_rfl, fun _ hp => isZero_oneStepObj_obj (by omega),
    fun _ => injective_gradedPiece_oneStepObj _ _ _⟩

/-! ### Biproducts of filtered objects

The biproduct `F^p (I ⊞ J) = F^p I ⊞ F^p J` is `FilteredObject.biprodObj`, and a morphism into it
from its two components is `FilteredObject.biprodObjLift`. -/

private lemma isIso_biprodObj_ι_app {I J : FilteredObject 𝒜 ℤᵒᵖ} {p : ℤ}
    (hI : IsIso (I.filtration.ι.app (op p))) (hJ : IsIso (J.filtration.ι.app (op p))) :
    IsIso ((biprodObj I J).filtration.ι.app (op p)) := by
  rw [biprodObj_ι_app]
  exact isIso_biprod_map _ _

private lemma isZero_biprodObj_obj {I J : FilteredObject 𝒜 ℤᵒᵖ} {p : ℤ}
    (hI : IsZero (I.filtration.obj (op p))) (hJ : IsZero (J.filtration.obj (op p))) :
    IsZero ((biprodObj I J).filtration.obj (op p)) := isZero_biprod hI hJ

/-- The steps of the filtration of a biproduct are the biproducts of the steps. -/
private lemma biprodObj_step (I J : FilteredObject 𝒜 ℤᵒᵖ) {i j : ℤᵒᵖ} (f : i ⟶ j) :
    (biprodObj I J).filtration.step f = biprod.map (I.filtration.step f) (J.filtration.step f) := by
  rw [← cancel_mono ((biprodObj I J).filtration.ι.app j), Filtration.step_comp_ι_app,
    biprodObj_ι_app, biprodObj_ι_app]
  apply biprod.hom_ext' <;> simp

/-- The graded pieces of a biproduct are the biproducts of the graded pieces, so the biproduct of
two filtered objects with injective graded pieces has injective graded pieces. -/
private lemma injective_gradedPiece_biprodObj {I J : FilteredObject 𝒜 ℤᵒᵖ} (p : ℤ)
    (hI : Injective ((gr p).obj I)) (hJ : Injective ((gr p).obj J)) :
    Injective ((gr p).obj (biprodObj I J)) := by
  have : Injective (cokernel (I.filtration.step (succHom p))) := hI
  have : Injective (cokernel (J.filtration.step (succHom p))) := hJ
  exact Injective.of_iso (cokernelIsoOfEq (biprodObj_step I J (succHom p)) ≪≫
    cokernelBiprodMapIso _ _).symm inferInstance

/-- The two components of a morphism into a biproduct of filtered objects are compatible with the
biproduct of the two filtrations. -/
private lemma biprod_lift_comp_biprod_map {A I J : FilteredObject 𝒜 ℤᵒᵖ} (f : A ⟶ I) (g : A ⟶ J)
    (i : ℤᵒᵖ) :
    biprod.lift (f.natTrans.app i) (g.natTrans.app i) ≫
        biprod.map (I.filtration.ι.app i) (J.filtration.ι.app i) =
      A.filtration.ι.app i ≫ biprod.lift f.hom g.hom := by
  apply biprod.hom_ext
  · simp [f.comm i]
  · simp [g.comm i]

/-- The `i`-th step of the quotient filtration of the cokernel of a strict morphism is an
isomorphism onto the cokernel as soon as the filtration of the target is exhausted at `i`. -/
private lemma isIso_cokernelStep {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u]
    (i : ℤᵒᵖ) (h : IsIso (I.filtration.ι.app i)) : IsIso (cokernelStep u i) := by
  have hepi : Epi (cokernel.π (u.natTrans.app i) ≫ cokernelStep u i) := by
    rw [π_comp_cokernelStep]; infer_instance
  have := epi_of_epi (cokernel.π (u.natTrans.app i)) (cokernelStep u i)
  exact isIso_of_mono_of_epi _

/-! ### The source's construction of a filtered injective object -/

/-- A monomorphism is the kernel of its cokernel: a morphism killed by `cokernel.π f` factors
through `f`. -/
private lemma exists_comp_eq_of_comp_cokernelπ_eq_zero {X Y : 𝒜} (f : X ⟶ Y) [Mono f] {T : 𝒜}
    (x : T ⟶ Y) (hx : x ≫ cokernel.π f = 0) : ∃ y : T ⟶ X, y ≫ f = x := by
  have h := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel f)
  exact ⟨h.lift (KernelFork.ofι x hx), h.fac (KernelFork.ofι x hx) WalkingParallelPair.zero⟩

/-- The injective object `I_c` of [Stacks, Tag 05TS]: an injective object of `𝒜` receiving the
quotient `A / F^{c + 1} A`. -/
private noncomputable abbrev stepInjective [EnoughInjectives 𝒜] (A : FilteredObject 𝒜 ℤᵒᵖ)
    (c : ℤ) : 𝒜 :=
  Injective.under (cokernel (A.filtration.ι.app (op (c + 1))))

/-- The morphism `u_c : A ⟶ I_c` of [Stacks, Tag 05TS]: the quotient `A ⟶ A / F^{c + 1} A`
followed by a monomorphism of that quotient into an injective object. Its kernel is `F^{c + 1} A`,
which is what makes the `c`-th filtration step of the direct sum of the `I_c` strict. -/
private noncomputable def toStepInjective [EnoughInjectives 𝒜] (A : FilteredObject 𝒜 ℤᵒᵖ)
    (c : ℤ) : A.X ⟶ stepInjective A c :=
  cokernel.π (A.filtration.ι.app (op (c + 1))) ≫ Injective.ι _

/-- `u_c : A ⟶ I_c` kills every filtration step above `c`. -/
private lemma ι_app_comp_toStepInjective [EnoughInjectives 𝒜] (A : FilteredObject 𝒜 ℤᵒᵖ) {c p : ℤ}
    (h : c + 1 ≤ p) : A.filtration.ι.app (op p) ≫ toStepInjective A c = 0 := by
  have h0 : A.filtration.ι.app (op (c + 1)) ≫ toStepInjective A c = 0 := by
    rw [toStepInjective, ← Category.assoc, cokernel.condition, zero_comp]
  rw [← A.filtration.diagram_map_comp_ι_app (homOfLE h).op, Category.assoc, h0, comp_zero]

/-- The kernel of `u_c : A ⟶ I_c` is `F^{c + 1} A`: a morphism to `A` killed by `u_c` factors
through the `(c + 1)`-st filtration step. -/
private lemma exists_comp_ι_app_eq_of_comp_toStepInjective_eq_zero [EnoughInjectives 𝒜]
    (A : FilteredObject 𝒜 ℤᵒᵖ) (c : ℤ) {T : 𝒜} (x : T ⟶ A.X) (hx : x ≫ toStepInjective A c = 0) :
    ∃ y : T ⟶ A.filtration.obj (op (c + 1)), y ≫ A.filtration.ι.app (op (c + 1)) = x := by
  refine exists_comp_eq_of_comp_cokernelπ_eq_zero _ x ?_
  rwa [← cancel_mono (Injective.ι (cokernel (A.filtration.ι.app (op (c + 1))))), zero_comp,
    Category.assoc]

/-- A filtration step of a morphism into a biproduct of filtered objects is a pullback square as
soon as that step of its second component is one and the corresponding step of the first factor
vanishes: where the first factor contributes nothing, the two squares have the same pullback. -/
private lemma isPullback_biprodObjLift {A J I : FilteredObject 𝒜 ℤᵒᵖ} (f : A ⟶ J) (g : A ⟶ I)
    {i : ℤᵒᵖ} (hJ : IsZero (J.filtration.obj i))
    (hg : IsPullback (g.natTrans.app i) (A.filtration.ι.app i) (I.filtration.ι.app i) g.hom) :
    IsPullback ((biprodObjLift f g).natTrans.app i) (A.filtration.ι.app i)
      ((biprodObj J I).filtration.ι.app i) (biprodObjLift f g).hom := by
  show IsPullback (biprod.lift (f.natTrans.app i) (g.natTrans.app i)) (A.filtration.ι.app i)
    (biprod.map (J.filtration.ι.app i) (I.filtration.ι.app i)) (biprod.lift f.hom g.hom)
  have key : ∀ s : PullbackCone (biprod.map (J.filtration.ι.app i) (I.filtration.ι.app i))
      (biprod.lift f.hom g.hom),
      (s.fst ≫ biprod.snd) ≫ I.filtration.ι.app i = s.snd ≫ g.hom := by
    intro s
    calc (s.fst ≫ biprod.snd) ≫ I.filtration.ι.app i
        = (s.fst ≫ biprod.map (J.filtration.ι.app i) (I.filtration.ι.app i)) ≫ biprod.snd := by
          simp
      _ = (s.snd ≫ biprod.lift f.hom g.hom) ≫ biprod.snd :=
          congrArg (fun t => t ≫ biprod.snd) s.condition
      _ = s.snd ≫ g.hom := by simp
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (biprod_lift_comp_biprod_map f g i)
    (fun s => hg.lift (s.fst ≫ biprod.snd) s.snd (key s)) (fun s => ?_)
    (fun s => hg.lift_snd _ _ _) (fun s m _ h₂ => ?_))
  · refine biprod.hom_ext _ _ (hJ.eq_of_tgt _ _) ?_
    rw [Category.assoc, biprod.lift_snd]
    exact hg.lift_fst _ _ _
  · rw [← cancel_mono (A.filtration.ι.app i), h₂, hg.lift_snd]

/-- The direct sum `⊕_{a ≤ m ≤ b} I_m` of [Stacks, Tag 05TS], filtered by
`F^p = ⊕_{m ≥ p} I_m` and receiving `A`, built by induction on the number `n + 1` of summands.
The `m`-th summand is an injective object receiving `A / F^{m + 1} A`, so the morphism `A ⟶ I` is a
monomorphism as soon as `F^{b + 1} A = 0`, which is the only hypothesis on `A`.

The filtration of `A` is *not* assumed to exhaust `A` at `a`, so the strictness squares are
pullbacks only from `a + 1` upwards: at `p ≤ a` the filtration of the target is already everything,
so the square there is a pullback precisely when `F^p A = A`. That is the form the induction can
carry, its step lowering `a` by one. -/
private lemma exists_biprodInjective [EnoughInjectives 𝒜] (n : ℕ) :
    ∀ (A : FilteredObject 𝒜 ℤᵒᵖ) (a b : ℤ), a + n = b → IsZero (A.filtration.obj (op (b + 1))) →
      ∃ (I : FilteredObject 𝒜 ℤᵒᵖ) (u : A ⟶ I),
        (∀ p : ℤ, a + 1 ≤ p → IsPullback (u.natTrans.app (op p)) (A.filtration.ι.app (op p))
          (I.filtration.ι.app (op p)) u.hom) ∧
        Mono u.hom ∧ IsIso (I.filtration.ι.app (op a)) ∧
        IsZero (I.filtration.obj (op (b + 1))) ∧
        ∀ p : ℤ, Injective ((gr p).obj I) := by
  induction n with
  | zero =>
    intro A a b hab hA
    obtain rfl : a = b := by simpa using hab
    have hAz : ∀ p : ℤ, a + 1 ≤ p → IsZero (A.filtration.obj (op p)) :=
      fun p hp => Filtration.isZero_obj_of_le A.filtration hp hA
    obtain ⟨hJiso, hJzero, hJinj⟩ := oneStepObj_spec (Injective.under A.X) a
    let u := oneStepHomMk (c := a) (Injective.ι A.X) fun p hp => (hAz p (by omega)).eq_of_src _ _
    have : Mono u.hom := inferInstanceAs (Mono (Injective.ι A.X))
    exact ⟨_, u, fun p hp => isPullback_of_isZero _ _ _ _ (hAz p hp) (hJzero p hp), inferInstance,
      hJiso, hJzero _ le_rfl, hJinj⟩
  | succ n ih =>
    intro A a b hab hA
    obtain ⟨I', u', hpb', hmono', hiso', hIzero', hinj'⟩ :=
      ih A (a + 1) b (by push_cast at hab ⊢; omega) hA
    obtain ⟨hJiso, hJzero, hJinj⟩ := oneStepObj_spec (stepInjective A a) a
    let J := oneStepObj (stepInjective A a) a
    let ua : A ⟶ J := oneStepHomMk (c := a) (toStepInjective A a)
      (fun p hp => ι_app_comp_toStepInjective A (by omega))
    have hbnd : a + 1 ≤ b := by push_cast at hab; omega
    have hsnd : (biprodObjLift ua u').hom ≫ biprod.snd = u'.hom := biprod.lift_snd _ _
    have : Mono (biprodObjLift ua u').hom := mono_of_mono_fac hsnd
    refine ⟨biprodObj _ I', biprodObjLift ua u', fun p hp => ?_, inferInstance,
      isIso_biprodObj_ι_app hJiso (Filtration.isIso_ι_app_of_le _ (by omega) hiso'),
      isZero_biprodObj_obj (hJzero _ (by omega)) hIzero',
      fun p => injective_gradedPiece_biprodObj p (hJinj p) (hinj' p)⟩
    rcases lt_or_ge p (a + 2) with h | h
    · obtain rfl : p = a + 1 := by omega
      have hzfst : (biprod.fst : J.filtration.obj (op (a + 1)) ⊞
          I'.filtration.obj (op (a + 1)) ⟶ _) = 0 :=
        (hJzero (a + 1) le_rfl).eq_of_tgt _ _
      have hw : (biprodObj J I').filtration.ι.app (op (a + 1)) ≫ biprod.fst = 0 := by
        show biprod.map (J.filtration.ι.app (op (a + 1)))
          (I'.filtration.ι.app (op (a + 1))) ≫ biprod.fst = 0
        rw [biprod.map_fst, hzfst, zero_comp]
      refine isPullback_of_factorsThru _ _ _ _ biprod.fst
        ((biprodObjLift ua u').comm (op (a + 1))) hw
        (fun T x hx => exists_comp_ι_app_eq_of_comp_toStepInjective_eq_zero A a x ?_)
      have hx' : x ≫ biprod.lift ua.hom u'.hom ≫ biprod.fst = 0 := hx
      rwa [biprod.lift_fst] at hx'
    · exact isPullback_biprodObjLift ua u' (hJzero p (by omega)) (hpb' p (by omega))

end Building

end CochainComplex.FilteredInjective.Resolution

end FilteredInjectiveResolutionDegreeZero

end
