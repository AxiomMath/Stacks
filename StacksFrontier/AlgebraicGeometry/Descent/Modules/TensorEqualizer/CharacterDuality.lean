module

public import Mathlib.Algebra.Module.CharacterModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.CharacterModule.Duality
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Pushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Module.SplitEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.UniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.CharacterModule
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Character duality for split equalizers and coequalizers

General facts about character modules used to tensor the equalizer of a module descent datum:
character duality reflects and preserves exactness, carries a split equalizer to a split
coequalizer, transports split coequalizers along sections and retractions and along tensoring
with a fixed module, and a split coequalizer of character-module duals makes a fork a limit.
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open CategoryTheory TensorProduct
open scoped ModuleCat.Algebra

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- A pair of linear maps is exact as soon as its pair of character-module duals is exact in the
opposite order. -/
public theorem exact_of_characterModule_dual_exact
    {S : Type*} [CommRing S]
    {M N P : Type*} [AddCommGroup M] [Module S M]
      [AddCommGroup N] [Module S N] [AddCommGroup P] [Module S P]
    (f : M →ₗ[S] N) (g : N →ₗ[S] P)
    (h : Function.Exact (CharacterModule.dual g) (CharacterModule.dual f)) :
    Function.Exact f g := by
  have hcomp : g.comp f = 0 := LinearMap.ext fun x =>
    CharacterModule.eq_zero_of_character_apply fun χ => congrArg (fun c : CharacterModule M => c x)
      (congrArg (fun k : CharacterModule P →ₗ[S] CharacterModule M => k χ)
        h.linearMap_comp_eq_zero)
  refine LinearMap.exact_of_comp_of_mem_range hcomp ?_
  intro x hx
  let q : N →ₗ[S] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  have hqx : q x = 0 := by
    apply CharacterModule.eq_zero_of_character_apply
    intro χ
    let ψ : CharacterModule N := CharacterModule.dual q χ
    have hψ : CharacterModule.dual f ψ = 0 := by
      have hqf : q.comp f = 0 := by
        ext y
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
      change (CharacterModule.dual f ∘ₗ CharacterModule.dual q) χ = 0
      rw [← CharacterModule.dual_comp f q, hqf, CharacterModule.dual_zero, LinearMap.zero_apply]
    obtain ⟨φ, hφ⟩ : ψ ∈ LinearMap.range (CharacterModule.dual g) := by
      rwa [← h.linearMap_ker_eq, LinearMap.mem_ker]
    have hev := congrArg (fun c : CharacterModule N => c x) hφ
    change χ (q x) = 0
    change φ (g x) = χ (q x) at hev
    rw [hx, map_zero] at hev
    exact hev.symm
  exact (Submodule.Quotient.mk_eq_zero _).mp hqx

/-- A split coequalizer `π` of `f` and `g` exhibits `π` as the cokernel of `g - f`. -/
public theorem function_exact_of_splitCoequalizer
    {S : Type u} [CommRing S]
    {U V W : Type w} [AddCommGroup U] [Module S U]
      [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
    (f g : U →ₗ[S] V) (π : V →ₗ[S] W)
    (h : IsSplitCoequalizer
      (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.ofHom π)) :
    Function.Exact (g - f) π := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro x
    have hc := congrArg (fun k : ModuleCat.of S U ⟶ ModuleCat.of S W => k.hom x)
      h.condition
    change π (f x) = π (g x) at hc
    simp [map_sub, hc]
  · intro x hx
    have hleft := congrArg (fun k : ModuleCat.of S V ⟶ ModuleCat.of S V => k.hom x)
      h.leftSection_bottom
    have htop := congrArg (fun k : ModuleCat.of S V ⟶ ModuleCat.of S V => k.hom x)
      h.leftSection_top
    have hx0 : π x = 0 := (LinearMap.mem_ker.mp hx)
    refine ⟨h.leftSection.hom x, ?_⟩
    change g (h.leftSection.hom x) - f (h.leftSection.hom x) = x
    change g (h.leftSection.hom x) = x at hleft
    change f (h.leftSection.hom x) = h.rightSection.hom (π x) at htop
    rw [hleft, htop, hx0, map_zero, sub_zero]

/-- Character duality is exact: the duals of an exact pair are exact in the opposite order. The
modules may live in a universe independent of the base ring, which is arranged by reading the
maps as linear over a universe-lifted copy of `ℤ`. -/
public theorem characterModule_dual_exact_any
    {R : Type u} [CommRing R] {A B C : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (CharacterModule.dual g) (CharacterModule.dual f) := by
  let _ : Module (ULift.{w} ℤ) A := Module.compHom A (ULift.ringEquiv (R := ℤ)).toRingHom
  let _ : Module (ULift.{w} ℤ) B := Module.compHom B (ULift.ringEquiv (R := ℤ)).toRingHom
  let _ : Module (ULift.{w} ℤ) C := Module.compHom C (ULift.ringEquiv (R := ℤ)).toRingHom
  let f' : A →ₗ[ULift.{w} ℤ] B :=
    { toFun := f, map_add' := f.map_add
      map_smul' := fun r a => map_zsmul f r.down a }
  let g' : B →ₗ[ULift.{w} ℤ] C :=
    { toFun := g, map_add' := g.map_add
      map_smul' := fun r b => map_zsmul g r.down b }
  exact CharacterModule.dual_exact f' g' (h : Function.Exact f' g')

/-- A split coequalizer of the character-module duals of `f, g, δ` transports to one of the duals
of `k, l, i` along sections `sP, sQ`, retractions `ρP, ρQ` and the naturality squares relating
them. Injectivity of `i` provides the surjection and the exactness hypothesis identifies the
kernel. -/
public noncomputable def characterDual_splitCoequalizer_of_splitCoequalizer
    {R : Type u} [CommRing R]
    {P Q Y I : Type w} [AddCommGroup P] [Module R P]
      [AddCommGroup Q] [Module R Q] [AddCommGroup Y] [Module R Y]
      [AddCommGroup I] [Module R I]
    (_u : P →ₗ[R] Q) (f g : Q →ₗ[R] Y) (δ : P →ₗ[R] Q)
    (i : I →ₗ[R] P) (k l : P →ₗ[R] Q)
    (hi : Function.Injective i)
    (hki : k.comp i = l.comp i)
    (hexact : Function.Exact i (l - k))
    (q : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f))
      (ModuleCat.ofHom (CharacterModule.dual g))
      (ModuleCat.ofHom (CharacterModule.dual δ)))
    (sP : CharacterModule P →ₗ[R] CharacterModule Q)
    (sQ : CharacterModule Q →ₗ[R] CharacterModule Y)
    (ρP : CharacterModule Q →ₗ[R] CharacterModule P)
    (ρQ : CharacterModule Y →ₗ[R] CharacterModule Q)
    (hsP : ρP.comp sP = LinearMap.id)
    (_hsQ : ρQ.comp sQ = LinearMap.id)
    (hNatK : sP.comp (CharacterModule.dual k) =
      (CharacterModule.dual f).comp sQ)
    (hNatL : sP.comp (CharacterModule.dual l) =
      (CharacterModule.dual g).comp sQ)
    (hRetK : (CharacterModule.dual k).comp ρQ =
      ρP.comp (CharacterModule.dual f))
    (hRetL : (CharacterModule.dual l).comp ρQ =
      ρP.comp (CharacterModule.dual g))
    (hδi : (CharacterModule.dual i).comp ρP =
      (CharacterModule.dual i).comp (CharacterModule.dual δ)) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual k))
      (ModuleCat.ofHom (CharacterModule.dual l))
      (ModuleCat.ofHom (CharacterModule.dual i)) := by
  let α := CharacterModule.dual k
  let β := CharacterModule.dual l
  let π := CharacterModule.dual i
  let α₁ := CharacterModule.dual f
  let β₁ := CharacterModule.dual g
  let π₁ := CharacterModule.dual δ
  let r₁ := q.rightSection.hom
  let t₁ := q.leftSection.hom
  have hqCond : π₁.comp α₁ = π₁.comp β₁ := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      congrArg ModuleCat.Hom.hom q.condition
  have hqπ : π₁.comp r₁ = LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
      congrArg ModuleCat.Hom.hom q.rightSection_π
  have hqBottom : β₁.comp t₁ = LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
      congrArg ModuleCat.Hom.hom q.leftSection_bottom
  have hqTop : α₁.comp t₁ = r₁.comp π₁ := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      congrArg ModuleCat.Hom.hom q.leftSection_top
  let t := (ρQ.comp t₁).comp sP
  let γ := ((ρP.comp r₁).comp π₁).comp sP
  have hγ : γ.comp α = γ.comp β := by
    dsimp [γ, α, β]
    simp only [LinearMap.comp_assoc]
    rw [hNatK, hNatL]
    change ρP.comp (r₁.comp ((π₁.comp (CharacterModule.dual f)).comp sQ)) =
      ρP.comp (r₁.comp ((π₁.comp (CharacterModule.dual g)).comp sQ))
    rw [hqCond]
  have hdualSub : CharacterModule.dual (l - k) =
      CharacterModule.dual l - CharacterModule.dual k := by
    ext χ x
    change χ ((l - k) x) = χ (l x) - χ (k x)
    simp [LinearMap.sub_apply, map_sub]
  have hdualExact := characterModule_dual_exact_any i (l - k) hexact
  have hkerEq : LinearMap.range (β - α) = LinearMap.ker π := by
    rw [← hdualSub]
    exact (LinearMap.exact_iff.mp hdualExact).symm
  have hker : LinearMap.ker π ≤ LinearMap.ker γ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    obtain ⟨z, rfl⟩ : x ∈ LinearMap.range (β - α) := by rwa [hkerEq]
    change γ (β z - α z) = 0
    rw [map_sub]
    have hz := congrArg (fun F : CharacterModule Q →ₗ[R]
        CharacterModule P => F z) hγ
    change γ (α z) = γ (β z) at hz
    rw [hz, sub_self]
  have hπsurj : Function.Surjective π :=
    (CharacterModule.dual_surjective_iff_injective).mpr hi
  let r : CharacterModule I →ₗ[R] CharacterModule P :=
    (LinearMap.ker π).liftQ γ hker ∘ₗ
      (π.quotKerEquivOfSurjective hπsurj).symm.toLinearMap
  have hrπ : r.comp π = γ := by
    ext x
    simp [r]
  have hπγ : π.comp γ = π := LinearMap.ext fun x => by
    change π (ρP (r₁ (π₁ (sP x)))) = π x
    have hδ := DFunLike.congr_fun hδi (r₁ (π₁ (sP x)))
    change π (ρP (r₁ (π₁ (sP x)))) = π (π₁ (r₁ (π₁ (sP x)))) at hδ
    have hq := DFunLike.congr_fun hqπ (π₁ (sP x))
    change π₁ (r₁ (π₁ (sP x))) = π₁ (sP x) at hq
    have hs := DFunLike.congr_fun hsP x
    change ρP (sP x) = x at hs
    have hδs := DFunLike.congr_fun hδi (sP x)
    change π (ρP (sP x)) = π (π₁ (sP x)) at hδs
    rw [hδ, hq, ← hδs, hs]
  have hπr : π.comp r = LinearMap.id := LinearMap.ext fun z => by
    obtain ⟨x, rfl⟩ := hπsurj z
    exact (congrArg π (DFunLike.congr_fun hrπ x)).trans (DFunLike.congr_fun hπγ x)
  refine {
    rightSection := ModuleCat.ofHom r
    leftSection := ModuleCat.ofHom t
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }
  · apply ModuleCat.hom_ext
    have hh : (CharacterModule.dual i).comp (CharacterModule.dual k) =
        (CharacterModule.dual i).comp (CharacterModule.dual l) := by
      rw [← CharacterModule.dual_comp i k, ← CharacterModule.dual_comp i l, hki]
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hh
  · apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using hπr
  · apply ModuleCat.hom_ext
    have hh : β.comp t = LinearMap.id := by
      dsimp [β, t]
      calc
        β.comp ((ρQ.comp t₁).comp sP) = ((β.comp ρQ).comp t₁).comp sP := by
          simp [LinearMap.comp_assoc]
        _ = ((ρP.comp β₁).comp t₁).comp sP := by rw [hRetL]
        _ = (ρP.comp (β₁.comp t₁)).comp sP := by simp [LinearMap.comp_assoc]
        _ = ρP.comp sP := by rw [hqBottom]; simp
        _ = LinearMap.id := hsP
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using hh
  · apply ModuleCat.hom_ext
    have hh : α.comp t = r.comp π := by
      dsimp [α, t]
      calc
        α.comp ((ρQ.comp t₁).comp sP) = ((α.comp ρQ).comp t₁).comp sP := by
          simp [LinearMap.comp_assoc]
        _ = ((ρP.comp α₁).comp t₁).comp sP := by rw [hRetK]
        _ = (ρP.comp (α₁.comp t₁)).comp sP := by simp [LinearMap.comp_assoc]
        _ = (ρP.comp (r₁.comp π₁)).comp sP := by rw [hqTop]
        _ = γ := by simp [γ, LinearMap.comp_assoc]
        _ = r.comp π := hrπ.symm
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hh

/-- A split coequalizer of the character-module duals of a fork makes the fork a limit. -/
public noncomputable def isLimitFork_of_characterDual_splitCoequalizer
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {K X Y : Type w}
    [AddCommGroup K] [Module A K] [Module R K] [IsScalarTower R A K]
    [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]
    [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower R A Y]
    (i : K →ₗ[A] X) (f g : X →ₗ[A] Y)
    (hcond : ModuleCat.ofHom i ≫ ModuleCat.ofHom f =
      ModuleCat.ofHom i ≫ ModuleCat.ofHom g)
    (hsplit : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual (f.restrictScalars R)))
      (ModuleCat.ofHom (CharacterModule.dual (g.restrictScalars R)))
      (ModuleCat.ofHom (CharacterModule.dual (i.restrictScalars R)))) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.Fork.ofι (ModuleCat.ofHom i) hcond) := by
  let iR := i.restrictScalars R
  let fR := f.restrictScalars R
  let gR := g.restrictScalars R
  have hsurj : Function.Surjective (CharacterModule.dual iR) := fun χ =>
    ⟨hsplit.rightSection.hom χ, congrArg
      (fun k : ModuleCat.of R (CharacterModule K) ⟶
        ModuleCat.of R (CharacterModule K) => k.hom χ) hsplit.rightSection_π⟩
  have hiR : Function.Injective iR :=
    (CharacterModule.dual_surjective_iff_injective).mp hsurj
  have hi : Function.Injective i := hiR
  have hdualExact₀ := function_exact_of_splitCoequalizer
    (CharacterModule.dual fR) (CharacterModule.dual gR)
    (CharacterModule.dual iR) hsplit
  have hdualEq : CharacterModule.dual (gR - fR) =
      CharacterModule.dual gR - CharacterModule.dual fR := by
    ext χ x
    change χ ((gR - fR) x) = χ (gR x) - χ (fR x)
    rw [LinearMap.sub_apply, map_sub]
  have hdualExact : Function.Exact (CharacterModule.dual (gR - fR))
      (CharacterModule.dual iR) := by
    rwa [hdualEq]
  have hexactR : Function.Exact iR (gR - fR) :=
    exact_of_characterModule_dual_exact iR (gR - fR) hdualExact
  let e : K ≃ₗ[A] LinearMap.range i :=
    LinearEquiv.ofBijective (LinearMap.rangeRestrict i) ⟨
      (fun x y hxy => hi (congrArg Subtype.val hxy)), by
        rintro ⟨y, x, rfl⟩
        exact ⟨x, rfl⟩⟩
  refine CategoryTheory.Limits.Fork.IsLimit.mk' _ fun s => ?_
  have hmem (x : s.pt) : s.ι.hom x ∈ LinearMap.range i := by
    have hker : s.ι.hom x ∈ LinearMap.ker (gR - fR) := by
      apply LinearMap.mem_ker.mpr
      change (g - f) (s.ι.hom x) = 0
      have h := congrArg (fun k : ModuleCat.of A s.pt ⟶ ModuleCat.of A Y => k.hom x)
        s.condition
      change f (s.ι.hom x) = g (s.ι.hom x) at h
      simp [h]
    have hrange : s.ι.hom x ∈ LinearMap.range iR := by
      rwa [← (LinearMap.exact_iff.mp hexactR)]
    rcases hrange with ⟨y, hy⟩
    exact ⟨y, by simpa [iR] using hy⟩
  let c : s.pt →ₗ[A] LinearMap.range i :=
    LinearMap.codRestrict (LinearMap.range i) s.ι.hom hmem
  let l : s.pt →ₗ[A] K := e.symm.toLinearMap.comp c
  refine ⟨ModuleCat.ofHom l, ?_, ?_⟩
  · ext x
    exact congrArg Subtype.val (e.apply_symm_apply (c x))
  · intro m hm
    ext x
    have h₁ := congrArg (fun k : ModuleCat.of A s.pt ⟶ ModuleCat.of A X => k.hom x) hm
    have h₂ : i (l x) = s.ι.hom x := congrArg Subtype.val (e.apply_symm_apply (c x))
    have h₁' : i (m.hom x) = s.ι.hom x := by
      change (m ≫ (CategoryTheory.Limits.Fork.ofι (ModuleCat.ofHom i) hcond).ι).hom x = _ at h₁
      simpa using h₁
    exact hi (h₁'.trans h₂.symm)

/-- The functorial character-module section of a composite is the composite of the sections. -/
public theorem functorialCharacterModuleSection_comp
    {R : Type u} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (g : CharacterModule M →ₗ[R] CharacterModule N)
    (h : CharacterModule N →ₗ[R] CharacterModule P)
    (A : Type*) [AddCommGroup A] [Module R A] :
    _root_.functorialCharacterModuleSection (h.comp g) A =
      (_root_.functorialCharacterModuleSection h A).comp
        (_root_.functorialCharacterModuleSection g A) :=
  rfl

/-- The functorial character-module section of the identity is the identity. -/
public theorem functorialCharacterModuleSection_id
    {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (A : Type*) [AddCommGroup A] [Module R A] :
    _root_.functorialCharacterModuleSection (LinearMap.id : CharacterModule M →ₗ[R]
      CharacterModule M) A = LinearMap.id := by
  ext χ
  simp [_root_.functorialCharacterModuleSection]

/-- The functorial section attached to a dual map is the dual of the map tensored with `A`. The
modules may live in a universe independent of `A`. -/
theorem functorialCharacterModuleSection_dual_lTensor_any
    {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]
    {P Q : Type w} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) :
    _root_.functorialCharacterModuleSection (CharacterModule.dual f) A =
      CharacterModule.dual (LinearMap.lTensor A f) := by
  refine LinearMap.ext fun χ => ?_
  apply CharacterModule.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      change ((_root_.functorialCharacterModuleSection
        (CharacterModule.dual f) A) χ) (z + z') =
        χ ((LinearMap.lTensor A f) (z + z'))
      rw [map_add, hz, hz', map_add, map_add]
      rfl
  | tmul a x => rfl

/-- Tensoring with `A` carries a split coequalizer of character-module duals to a split
coequalizer of the duals of the tensored maps. The modules may live in a universe independent
of `A`. -/
noncomputable def characterDual_splitCoequalizer_tensor_any
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {P Q I : Type w} [AddCommGroup P] [Module R P]
      [AddCommGroup Q] [Module R Q] [AddCommGroup I] [Module R I]
    {f g : P →ₗ[R] Q} {π : I →ₗ[R] P}
    (q : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f))
      (ModuleCat.ofHom (CharacterModule.dual g))
      (ModuleCat.ofHom (CharacterModule.dual π))) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual (LinearMap.lTensor A f)))
      (ModuleCat.ofHom (CharacterModule.dual (LinearMap.lTensor A g)))
      (ModuleCat.ofHom (CharacterModule.dual (LinearMap.lTensor A π))) := by
  refine {
    rightSection := ModuleCat.ofHom
      (_root_.functorialCharacterModuleSection q.rightSection.hom A)
    leftSection := ModuleCat.ofHom
      (_root_.functorialCharacterModuleSection q.leftSection.hom A)
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h : (CharacterModule.dual π).comp (CharacterModule.dual f) =
        (CharacterModule.dual π).comp (CharacterModule.dual g) :=
      congrArg ModuleCat.Hom.hom q.condition
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_dual_lTensor_any] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h : (CharacterModule.dual π).comp q.rightSection.hom = LinearMap.id :=
      congrArg ModuleCat.Hom.hom q.rightSection_π
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_id,
      functorialCharacterModuleSection_dual_lTensor_any] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h : (CharacterModule.dual g).comp q.leftSection.hom = LinearMap.id :=
      congrArg ModuleCat.Hom.hom q.leftSection_bottom
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_id,
      functorialCharacterModuleSection_dual_lTensor_any] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h : (CharacterModule.dual f).comp q.leftSection.hom =
        q.rightSection.hom.comp (CharacterModule.dual π) :=
      congrArg ModuleCat.Hom.hom q.leftSection_top
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_dual_lTensor_any] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h

/-- Tensoring with `A` carries a split coequalizer of character-module duals to a split
coequalizer of the duals of the tensored maps. -/
public noncomputable def characterDual_splitCoequalizer_tensor
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    {f g : ModuleCat.of R (CharacterModule N) ⟶ ModuleCat.of R (CharacterModule M)}
    {π : ModuleCat.of R (CharacterModule M) ⟶ ModuleCat.of R (CharacterModule P)}
    (q : IsSplitCoequalizer f g π) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (_root_.functorialCharacterModuleSection f.hom A))
      (ModuleCat.ofHom (_root_.functorialCharacterModuleSection g.hom A))
      (ModuleCat.ofHom (_root_.functorialCharacterModuleSection π.hom A)) := by
  refine {
    rightSection := ModuleCat.ofHom
      (_root_.functorialCharacterModuleSection q.rightSection.hom A)
    leftSection := ModuleCat.ofHom
      (_root_.functorialCharacterModuleSection q.leftSection.hom A)
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h : π.hom.comp f.hom = π.hom.comp g.hom :=
      congrArg ModuleCat.Hom.hom q.condition
    simpa only [functorialCharacterModuleSection_comp] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h : π.hom.comp q.rightSection.hom = LinearMap.id :=
      congrArg ModuleCat.Hom.hom q.rightSection_π
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_id] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h : g.hom.comp q.leftSection.hom = LinearMap.id :=
      congrArg ModuleCat.Hom.hom q.leftSection_bottom
    simpa only [functorialCharacterModuleSection_comp,
      functorialCharacterModuleSection_id] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h : f.hom.comp q.leftSection.hom = q.rightSection.hom.comp π.hom :=
      congrArg ModuleCat.Hom.hom q.leftSection_top
    simpa only [functorialCharacterModuleSection_comp] using
      congrArg (fun k => _root_.functorialCharacterModuleSection k A) h

/-- The functorial section attached to a dual map is the dual of the map tensored with `A`. -/
public theorem functorialCharacterModuleSection_dual_lTensor
    {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]
    {P Q : Type v} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) :
    _root_.functorialCharacterModuleSection (CharacterModule.dual f) A =
      CharacterModule.dual (LinearMap.lTensor A f) :=
  functorialCharacterModuleSection_dual_lTensor_any f

/-- The character-module dual of the identity is the identity. -/
public theorem characterModule_dual_id
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P] :
    CharacterModule.dual (LinearMap.id : P →ₗ[R] P) = LinearMap.id :=
  rfl

/-- Character duality carries a split equalizer to a split coequalizer. -/
public noncomputable def characterDual_splitCoequalizer_of_splitEqualizer
    {R : Type u} [CommRing R] {P Q Y : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (f g : Q →ₗ[R] Y)
    (h : IsSplitEqualizer (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.ofHom i)) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f))
      (ModuleCat.ofHom (CharacterModule.dual g))
      (ModuleCat.ofHom (CharacterModule.dual i)) := by
  refine {
    rightSection := ModuleCat.ofHom (CharacterModule.dual h.leftRetraction.hom)
    leftSection := ModuleCat.ofHom (CharacterModule.dual h.rightRetraction.hom)
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [← CharacterModule.dual_comp i f, ← CharacterModule.dual_comp i g]
    have hh' : f.comp i = g.comp i := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
        congrArg ModuleCat.Hom.hom h.condition
    exact congrArg CharacterModule.dual hh'
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    rw [← CharacterModule.dual_comp i h.leftRetraction.hom]
    have hh' : h.leftRetraction.hom.comp i = LinearMap.id := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
        congrArg ModuleCat.Hom.hom h.ι_leftRetraction
    simpa only [characterModule_dual_id] using
      congrArg (fun k => CharacterModule.dual k) hh'
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    rw [← CharacterModule.dual_comp g h.rightRetraction.hom]
    have hh' : h.rightRetraction.hom.comp g = LinearMap.id := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
        congrArg ModuleCat.Hom.hom h.bottom_rightRetraction
    simpa only [characterModule_dual_id] using
      congrArg (fun k => CharacterModule.dual k) hh'
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have hh' : h.rightRetraction.hom.comp f = i.comp h.leftRetraction.hom := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
        congrArg ModuleCat.Hom.hom h.top_rightRetraction
    rw [← CharacterModule.dual_comp h.leftRetraction.hom i]
    exact congrArg (fun k => CharacterModule.dual k) hh'

end ModuleCat

end
