module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration.SubobjectChains

/-!
# Filtrations by direct images of integral ideal sheaves as bundled data

The structure `IntegralFiltrationData F` bundles a filtration of a module `F` as in
[Stacks, Tag 01YF], together with its constructions: the trivial filtration of a zero module,
transport along an isomorphism, concatenation along a short exact sequence, and the inductive
step on an irreducible support whose generic stalk is killed by the maximal ideal. The supports
of monomorphisms and cokernels needed for that step are also recorded here.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.DevissageNoetherian (isClosed_supp_of_isCoherent
  isZero_of_supp_eq_empty)
open Stacks.AlgebraicGeometry.IrreducibleDevissage (supp_subset_of_epi)
open Stacks.AlgebraicGeometry.RegularIdealSheaf (kernelSubmodule definingIdealOfHom
  mem_definingIdealOfHom)
open Stacks.SheafOfModules.OnSpace (sheafHom)

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### Supports -/

/-- A coherent module whose support lies in a closed set and misses its generic point is
supported strictly inside it. -/
theorem supp_ssubset_of_genericPoint_notMem {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent] {T : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ T)
    (hFT : SheafOfModules.supp F ⊆ T)
    (hξF : ξ ∉ SheafOfModules.supp F) :
    SheafOfModules.supp F ⊂ T :=
  ⟨hFT, fun heq => hξF ((hξ.mem_closed_set_iff (isClosed_supp_of_isCoherent F inferInstance)).2
    heq)⟩

/-- A point at which a morphism is surjective on stalks is not in the support of its
cokernel. -/
theorem notMem_supp_cokernel_of_stalk_surjective {X : Scheme.{u}}
    {F G : X.Modules} (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f)).hom)) :
    x ∉ SheafOfModules.supp (cokernel f) := by
  intro hx
  obtain ⟨b, hb⟩ := hx
  let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  have hz : T.map f ≫ T.map (cokernel.π f) = 0 := by
    rw [← T.map_comp, cokernel.condition, T.map_zero]
  have hsurj : Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf (cokernel.π f))).hom) := by
    have hepi : Epi (C := _root_.SheafOfModules.{u} X.ringCatSheaf) (cokernel.π f) :=
      inferInstanceAs (Epi (cokernel.π f))
    exact (AlgebraicGeometry.epi_iff_stalk_surjective X.ringCatSheaf (cokernel.π f)).mp hepi x
  obtain ⟨a, ha⟩ := hsurj b
  obtain ⟨c, hc⟩ := hf a
  apply hb
  rw [← ha, ← hc]
  exact ConcreteCategory.congr_hom hz c

/-- A morphism that restricts to an isomorphism over an open has, at every point of that open,
a cokernel with vanishing stalk. -/
theorem notMem_supp_cokernel_of_isIso_restrict {X : Scheme.{u}}
    {F G : X.Modules} (f : F ⟶ G) (U : X.Opens) (x : X) (hx : x ∈ U)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] :
    x ∉ SheafOfModules.supp (cokernel f) := by
  let xU : U.toScheme := ⟨x, hx⟩
  let E := Scheme.Modules.restrictStalkNatIso U.ι xU
  let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι xU)
  let R := Scheme.Modules.restrictFunctor U.ι ⋙
    Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} xU
  have hR : IsIso (R.map f) := by
    change IsIso ((Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} xU).map
        ((Scheme.Modules.restrictFunctor U.ι).map f))
    infer_instance
  have hT : IsIso (T.map f) := by
    have hcomp : IsIso (E.hom.app F ≫ T.map f) := by
      rw [← E.hom.naturality f]
      infer_instance
    exact IsIso.of_isIso_comp_left (E.hom.app F) (T.map f)
  have hxeq : U.ι xU = x := rfl
  apply notMem_supp_cokernel_of_stalk_surjective f x
  have hs := (ConcreteCategory.bijective_of_isIso (T.map f)).2
  change Function.Surjective (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor Ab (U.ι xU)).map
      (Scheme.Modules.Hom.mapPresheaf f))) at hs
  rwa [hxeq] at hs

/-- The image of the generic point of an integral closed subscheme is the generic point of its
image. -/
theorem isGenericPoint_range_of_isClosedImmersion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {η : Z}
    (hη : IsGenericPoint η (Set.univ : Set Z)) :
    IsGenericPoint (i η) (Set.range i) := by
  simpa [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] using
    hη.image i.continuous

/-! ### The filtration as bundled data -/

/-- A filtration of `F` as in [Stacks, Tag 01YF]: a monotone chain of subobjects from `⊥` to
`⊤` with coherent terms, each successive quotient being the direct image of a nonzero coherent
sheaf of ideals on an integral closed subscheme. -/
structure IntegralFiltrationData {X : Scheme.{u}} (F : X.Modules) where
  /-- The length of the filtration. -/
  length : ℕ
  /-- The terms of the filtration. -/
  step : Fin (length + 1) → Subobject F
  /-- The filtration is increasing. -/
  monotone : Monotone step
  /-- The filtration starts at the zero submodule. -/
  start : step 0 = ⊥
  /-- The filtration ends at `F`. -/
  finish : step (Fin.last length) = ⊤
  /-- Every term of the filtration is coherent. -/
  coherent : ∀ j, (step j : X.Modules).IsCoherent
  /-- Every successive quotient is the direct image of a nonzero coherent sheaf of ideals on an
  integral closed subscheme. -/
  factor : ∀ j : Fin length,
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i)
      (_ : IsIntegral Z)
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent ∧ ¬ IsZero I.toSheafOfModules ∧
      Nonempty (cokernel (Subobject.ofLE (step j.castSucc) (step j.succ)
        (monotone j.castSucc_le_succ)) ≅
        (Scheme.Modules.pushforward i).obj I.toSheafOfModules)

/-- A module carrying such a filtration is coherent, being the last term of the filtration. -/
theorem IntegralFiltrationData.isCoherent
    {X : Scheme.{u}} {F : X.Modules} (D : IntegralFiltrationData F) :
    F.IsCoherent :=
  let e : F ≅ ((D.step (Fin.last D.length) : Subobject F) : X.Modules) :=
    (Subobject.underlyingIso (𝟙 F)).symm ≪≫
      eqToIso (congrArg (fun T : Subobject F => (T : X.Modules))
        ((Subobject.mk_eq_top_of_isIso (𝟙 F)).symm.trans D.finish.symm))
  @isCoherent_of_iso _ _ _ _ _ e (D.coherent (Fin.last D.length))

/-- A module isomorphic to the direct image of a nonzero coherent sheaf of ideals on an integral
closed subscheme has a filtration of length one. -/
def integralFiltrationData_of_single_factor
    {X : Scheme.{u}} {F : X.Modules} (hF : F.IsCoherent)
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsCoherent) (hInz : ¬ IsZero I.toSheafOfModules)
    (e : F ≅ (Scheme.Modules.pushforward i).obj I.toSheafOfModules) :
    IntegralFiltrationData F := by
  classical
  let step : Fin 2 → Subobject F := fun j => if j = 0 then ⊥ else ⊤
  have hstart : step 0 = ⊥ := by simp [step]
  have hfinish : step (Fin.last 1) = ⊤ := by simp [step]
  have hmono : Monotone step := by
    intro j k hjk
    by_cases hj : j = 0
    · simp [step, hj]
    · have hk : k ≠ 0 := by
        rintro rfl
        exact hj (Fin.le_zero_iff.mp hjk)
      simp [step, hj, hk]
  have htopObj : ((step (Fin.last 1) : Subobject F) : X.Modules) =
      ((Subobject.mk (𝟙 F) : Subobject F) : X.Modules) :=
    congrArg (fun P : Subobject F => (P : X.Modules))
      (hfinish.trans (Subobject.mk_eq_top_of_isIso (𝟙 F)).symm)
  let eTop : ((step (Fin.last 1) : Subobject F) : X.Modules) ≅ F :=
    (eqToIso htopObj) ≪≫ Subobject.underlyingIso (𝟙 F)
  have hcoh : ∀ j : Fin 2, (step j : X.Modules).IsCoherent := by
    intro j
    by_cases hj : j = 0
    · rw [hj]
      change ((⊥ : Subobject F) : X.Modules).IsCoherent
      exact isCoherent_of_isZero ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
    · have hj' : j = Fin.last 1 := by
        apply Fin.ext
        simp only [Fin.val_last]
        have hjval : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega
      rw [hj']
      exact @isCoherent_of_iso _ _ _ _ _ eTop hF
  refine ⟨1, step, hmono, hstart, hfinish, hcoh, ?_⟩
  intro j
  obtain rfl : j = 0 := Fin.ext (by omega)
  refine ⟨Z, i, inferInstance, inferInstance, I, hI, hInz, ?_⟩
  let f : ((step (0 : Fin 2) : Subobject F) : X.Modules) ⟶
      ((step (Fin.last 1) : Subobject F) : X.Modules) :=
    Subobject.ofLE (step 0) (step (Fin.last 1)) (hmono (by decide))
  have hbotObj : ((step (0 : Fin 2) : Subobject F) : X.Modules) =
      ((⊥ : Subobject F) : X.Modules) :=
    congrArg (fun P : Subobject F => (P : X.Modules)) hstart
  let eBot := (eqToIso hbotObj) ≪≫ Subobject.botCoeIsoZero
  have hf : f = 0 := zero_of_source_iso_zero f eBot
  let e₀ : cokernel f ≅ ((step (Fin.last 1) : Subobject F) : X.Modules) := by
    rw [hf]
    exact cokernelZeroIsoTarget
  exact ⟨e₀ ≪≫ eTop ≪≫ e⟩

/-- A zero module has a filtration of length zero. -/
def integralFiltrationData_of_isZero
    {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) : IntegralFiltrationData F :=
  ⟨0, fun _ => ⊥, fun _ _ _ => le_rfl, rfl, (Subobject.subsingleton_of_isZero hF).elim _ _,
    fun _ => isCoherent_of_isZero ((isZero_zero _).of_iso Subobject.botCoeIsoZero), Fin.elim0⟩

/-- A filtration transports along an isomorphism of modules. -/
def integralFiltrationData_of_iso
    {X : Scheme.{u}} [IsNoetherian X] {F G : X.Modules} (e : F ≅ G)
    (D : IntegralFiltrationData F) : IntegralFiltrationData G := by
  classical
  let step : Fin (D.length + 1) → Subobject G :=
    fun j => (Subobject.map e.hom).obj (D.step j)
  have hmono : Monotone step := fun j k hjk =>
    (Subobject.map e.hom).monotone (D.monotone hjk)
  refine ⟨D.length, step, hmono, ?_, ?_, ?_, ?_⟩
  · dsimp [step]
    rw [D.start, Subobject.map_bot]
  · dsimp [step]
    rw [D.finish, Subobject.map_top]
    exact Subobject.mk_eq_top_of_isIso e.hom
  · intro j
    dsimp [step]
    exact @isCoherent_of_iso _ _ _ _ _ (subobjectMapObjIso e.hom (D.step j)).symm
      (D.coherent j)
  · intro j
    let e₁ := cokernelMapIso e.hom (D.step j.castSucc) (D.step j.succ)
      (D.monotone j.castSucc_le_succ)
    obtain ⟨Z, i, hi, hZ, I, hI, hInz, e₂⟩ := D.factor j
    exact ⟨Z, i, hi, hZ, I, hI, hInz, ⟨e₁ ≪≫ e₂.some⟩⟩

/-- Concatenating a filtration of the sub and a filtration of the quotient filters the middle
term of a short exact sequence, provided the quotient's filtration is not trivial. -/
def integralFiltrationData_of_shortExact
    {X : Scheme.{u}} [IsNoetherian X] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hF : S.X₂.IsCoherent) (hQambient : S.X₃.IsCoherent)
    (A : IntegralFiltrationData S.X₁) (Q : IntegralFiltrationData S.X₃)
    (hQ : 0 < Q.length) : IntegralFiltrationData S.X₂ := by
  classical
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  have hbound : (Subobject.map S.f).obj ⊤ = (Subobject.pullback S.g).obj ⊥ := by
    rw [Subobject.pullback_bot]
    exact map_top_eq_kernelSubobject S hS hS.mono_f
  let f : Fin (A.length + 1) → Subobject S.X₂ :=
    fun j => (Subobject.map S.f).obj (A.step j)
  let g : Fin (Q.length + 1) → Subobject S.X₂ :=
    fun j => (Subobject.pullback S.g).obj (Q.step j)
  let step := appendFinSequence f g
  have hjoin : f (Fin.last A.length) = g 0 := by
    dsimp [f, g]
    rw [A.finish, Q.start, hbound]
  have hmono : Monotone step := appendFinSequence_monotone f g
    (fun j => (Subobject.map S.f).monotone (A.monotone j.castSucc_le_succ))
    (fun j => (Subobject.pullback S.g).monotone (Q.monotone j.castSucc_le_succ)) hjoin hQ
  refine ⟨A.length + Q.length, step, hmono, ?_, ?_, ?_, ?_⟩
  · have hidx : (0 : Fin (A.length + Q.length + 1)) =
        Fin.cast (by omega : A.length + 1 + Q.length = A.length + Q.length + 1)
          (Fin.castAdd Q.length (0 : Fin (A.length + 1))) := by
      apply Fin.ext
      simp
    rw [hidx]
    change appendFinSequence f g _ = ⊥
    rw [appendFinSequence_left]
    dsimp [f]
    rw [A.start, Subobject.map_bot]
  · let k : Fin Q.length := ⟨Q.length - 1, by omega⟩
    have hk : k.succ = Fin.last Q.length := by
      apply Fin.ext
      simp [k]
      omega
    have hidx : Fin.last (A.length + Q.length) =
        Fin.cast (by omega : A.length + 1 + Q.length = A.length + Q.length + 1)
          (Fin.natAdd (A.length + 1) k) := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_cast, Fin.val_natAdd]
      dsimp [k]
      omega
    rw [hidx]
    change appendFinSequence f g _ = ⊤
    rw [appendFinSequence_right, hk]
    dsimp [g]
    rw [Q.finish, Subobject.pullback_top]
  · intro j
    have hcast : A.length + Q.length + 1 = (A.length + 1) + Q.length := by omega
    have hcoh : ∀ i : Fin ((A.length + 1) + Q.length),
        ((step (Fin.cast hcast.symm i) : Subobject S.X₂) : X.Modules).IsCoherent := by
      intro i
      refine Fin.addCases (m := A.length + 1) (n := Q.length) ?_ ?_ i
      · intro k
        change ((appendFinSequence f g
          (Fin.cast hcast.symm (Fin.castAdd Q.length k)) : Subobject S.X₂) :
            X.Modules).IsCoherent
        rw [appendFinSequence_left]
        dsimp [f]
        exact @isCoherent_of_iso _ _ _ _ _ (subobjectMapObjIso S.f (A.step k)).symm
          (A.coherent k)
      · intro k
        change ((appendFinSequence f g
          (Fin.cast hcast.symm (Fin.natAdd (A.length + 1) k)) : Subobject S.X₂) :
            X.Modules).IsCoherent
        rw [appendFinSequence_right]
        let P := (Subobject.pullback S.g).obj (Q.step k.succ)
        let d := S.g ≫ cokernel.π (Q.step k.succ).arrow
        have hP : P = kernelSubobject d := by
          simp [P, d, Abelian.Subobject.pullback_eq_kernelSubobject]
        have hc : (cokernel (Q.step k.succ).arrow).IsCoherent :=
          ProperMapping.isCoherent_cokernel (Q.coherent k.succ) hQambient
            (Q.step k.succ).arrow
        have hkcoh : (kernel d).IsCoherent := ProperMapping.isCoherent_kernel hF hc d
        have hscoh : (kernelSubobject d : X.Modules).IsCoherent :=
          @isCoherent_of_iso _ _ _ _ _ (Subobject.underlyingIso (kernel.ι d)) hkcoh
        change (P : X.Modules).IsCoherent
        rwa [hP]
    exact hcoh (Fin.cast hcast j)
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      let e₁ := cokernelMapIso S.f (A.step k.castSucc) (A.step k.succ)
        (A.monotone k.castSucc_le_succ)
      obtain ⟨Z, i, hi, hZ, I, hI, hInz, e₂⟩ := A.factor k
      refine ⟨Z, i, hi, hZ, I, hI, hInz, ?_⟩
      dsimp only [step]
      obtain ⟨e₀⟩ := cokernel_ofLE_congr (appendFinSequence_left_castSucc f g k)
        (appendFinSequence_left_succ f g k)
        (hmono (Fin.castSucc_le_succ (Fin.castAdd Q.length k)))
        ((Subobject.map S.f).monotone (A.monotone k.castSucc_le_succ))
      exact ⟨e₀ ≪≫ e₁ ≪≫ e₂.some⟩
    · intro k
      let e₁ := cokernelPullbackIso S.g (Q.step k.castSucc) (Q.step k.succ)
        (Q.monotone k.castSucc_le_succ)
      obtain ⟨Z, i, hi, hZ, I, hI, hInz, e₂⟩ := Q.factor k
      refine ⟨Z, i, hi, hZ, I, hI, hInz, ?_⟩
      by_cases hk : k.val = 0
      · have hk0 : k = (⟨0, hQ⟩ : Fin Q.length) := Fin.ext hk
        subst k
        dsimp only [step]
        have hsrc : appendFinSequence f g
            (Fin.natAdd A.length (⟨0, hQ⟩ : Fin Q.length)).castSucc =
              (Subobject.pullback S.g).obj (Q.step (⟨0, hQ⟩ : Fin Q.length).castSucc) := by
          calc
            _ = f (Fin.last A.length) := appendFinSequence_right_castSucc_zero f g hQ
            _ = (Subobject.map S.f).obj ⊤ := by dsimp [f]; rw [A.finish]
            _ = (Subobject.pullback S.g).obj ⊥ := hbound
            _ = (Subobject.pullback S.g).obj (Q.step (⟨0, hQ⟩ : Fin Q.length).castSucc) := by
              have hidx : (⟨0, hQ⟩ : Fin Q.length).castSucc = (0 : Fin (Q.length + 1)) := by
                apply Fin.ext
                simp
              have hQ0 : Q.step (⟨0, hQ⟩ : Fin Q.length).castSucc = ⊥ := by
                rw [hidx, Q.start]
              exact congrArg (fun P => (Subobject.pullback S.g).obj P) hQ0.symm
        have htgt : appendFinSequence f g
            (Fin.natAdd A.length (⟨0, hQ⟩ : Fin Q.length)).succ =
              (Subobject.pullback S.g).obj (Q.step (⟨0, hQ⟩ : Fin Q.length).succ) :=
          appendFinSequence_right_succ_zero f g hQ
        obtain ⟨e₀⟩ := cokernel_ofLE_congr hsrc htgt
          (hmono (Fin.castSucc_le_succ (Fin.natAdd A.length (⟨0, hQ⟩ : Fin Q.length))))
          ((Subobject.pullback S.g).monotone
            (Q.monotone (⟨0, hQ⟩ : Fin Q.length).castSucc_le_succ))
        exact ⟨e₀ ≪≫ e₁ ≪≫ e₂.some⟩
      · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
        dsimp only [step]
        have hsrc : appendFinSequence f g (Fin.natAdd A.length k).castSucc =
            (Subobject.pullback S.g).obj (Q.step k.castSucc) :=
          appendFinSequence_right_castSucc f g k hkpos
        have htgt : appendFinSequence f g (Fin.natAdd A.length k).succ =
            (Subobject.pullback S.g).obj (Q.step k.succ) :=
          appendFinSequence_right_step f g k
        obtain ⟨e₀⟩ := cokernel_ofLE_congr hsrc htgt
          (hmono (Fin.castSucc_le_succ (Fin.natAdd A.length k)))
          ((Subobject.pullback S.g).monotone (Q.monotone k.castSucc_le_succ))
        exact ⟨e₀ ≪≫ e₁ ≪≫ e₂.some⟩

/-- Concatenating a filtration of the sub and a filtration of the quotient filters the middle
term of a short exact sequence. If the quotient's filtration is trivial the quotient vanishes
and the first map is an isomorphism. -/
def integralFiltrationData_of_shortExact_any
    {X : Scheme.{u}} [IsNoetherian X] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hF : S.X₂.IsCoherent) (hQambient : S.X₃.IsCoherent)
    (A : IntegralFiltrationData S.X₁) (Q : IntegralFiltrationData S.X₃) :
    IntegralFiltrationData S.X₂ := by
  classical
  by_cases hn : 0 < Q.length
  · exact integralFiltrationData_of_shortExact S hS hF hQambient A Q hn
  · have hlen : Q.length = 0 := Nat.eq_zero_of_not_pos hn
    have hbotTop : (⊥ : Subobject S.X₃) = ⊤ := by
      calc
        _ = Q.step 0 := Q.start.symm
        _ = Q.step (Fin.last Q.length) := by
          rw [show Fin.last Q.length = (0 : Fin (Q.length + 1)) from Fin.ext (by simp [hlen])]
        _ = ⊤ := Q.finish
    have hzero : IsZero S.X₃ := (IsZero.iff_id_eq_zero S.X₃).2
      (Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_eq_top_of_isIso (𝟙 S.X₃)).trans hbotTop.symm))
    have hg : S.g = 0 := hzero.eq_of_tgt S.g 0
    let K : KernelFork S.g := KernelFork.ofι (𝟙 S.X₂) (by rw [hg]; simp)
    let l : S.X₂ ⟶ S.X₁ := hS.fIsKernel.lift K
    have hl : l ≫ S.f = 𝟙 S.X₂ := by
      simpa [l, K] using hS.fIsKernel.fac K WalkingParallelPair.zero
    letI : IsSplitEpi S.f := IsSplitEpi.mk' ⟨l, hl⟩
    letI : Mono S.f := hS.mono_f
    have hIso : IsIso S.f := isIso_of_mono_of_isSplitEpi S.f
    exact integralFiltrationData_of_iso (asIso S.f) A

/-- A filtration of a submodule and a filtration of the corresponding quotient filter the
ambient module. -/
def integralFiltrationData_of_mono_cokernel
    {X : Scheme.{u}} [IsNoetherian X] {A F : X.Modules}
    (f : A ⟶ F) (hf : Mono f) (hA : A.IsCoherent) (hF : F.IsCoherent)
    (DA : IntegralFiltrationData A)
    (DQ : IntegralFiltrationData (cokernel f)) :
    IntegralFiltrationData F :=
  letI := hf
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
      (by change Mono f; infer_instance) (by dsimp [S]; infer_instance)
  integralFiltrationData_of_shortExact_any S hS hF
    (ProperMapping.isCoherent_cokernel hA hF f) DA DQ

/-- Filtrations of the two summands filter their biproduct. -/
def integralFiltrationData_of_biprod
    {X : Scheme.{u}} [IsNoetherian X] {A B : X.Modules}
    (hAB : (A ⊞ B).IsCoherent) (hB : B.IsCoherent)
    (DA : IntegralFiltrationData A) (DB : IntegralFiltrationData B) :
    IntegralFiltrationData (A ⊞ B) :=
  integralFiltrationData_of_shortExact_any
    (ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact hAB hB DA DB

/-- The direct image of a finite sum of copies of a nonzero coherent sheaf of ideals on an
integral closed subscheme has a filtration whose every quotient is that direct image. -/
def integralFiltrationData_of_repeated_factor
    {X Z : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z]
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsCoherent)
    (hInz : ¬ IsZero I.toSheafOfModules) (n : ℕ) :
    IntegralFiltrationData ((Scheme.Modules.pushforward i).obj
      (∐ fun _ : Fin n => I.toSheafOfModules)) := by
  classical
  let P := (Scheme.Modules.pushforward i).obj I.toSheafOfModules
  letI : I.toSheafOfModules.IsQuasicoherent :=
    isQuasicoherent_of_isCoherent I.toSheafOfModules
  have hP : P.IsCoherent :=
    PushforwardCoherent.pushforward_isCoherent_of_isFinite i I.toSheafOfModules
  have hRepeat : ∀ n : ℕ, IntegralFiltrationData (∐ fun _ : Fin n => P) := by
    intro n
    induction n with
    | zero =>
      exact integralFiltrationData_of_isZero (IsInitial.isZero
        ((isColimitEquivIsInitialOfIsEmpty X.Modules
          (Cofan.mk (∐ fun _ : Fin 0 => P) (Sigma.ι (fun _ : Fin 0 => P)))).toFun
          (colimit.isColimit (Discrete.functor (fun _ : Fin 0 => P)))))
    | succ n ih =>
      let A := ∐ fun _ : Fin n => P
      have hA : A.IsCoherent := ih.isCoherent
      have hB : (A ⊞ P).IsCoherent :=
        ProperMapping.isCoherent_X₂_of_shortExact
          (ShortComplex.Splitting.ofHasBinaryBiproduct A P).shortExact hA hP
      let D := integralFiltrationData_of_biprod hB hP ih
        (integralFiltrationData_of_single_factor hP i I hI hInz (Iso.refl P))
      let e : (∐ fun _ : Fin (n + 1) => P) ≅ A ⊞ P :=
        coproductFinSuccIso P n ≪≫ (biprod.isoCoprod A P).symm
      exact integralFiltrationData_of_iso e.symm D
  exact integralFiltrationData_of_iso
    (PreservesCoproduct.iso (Scheme.Modules.pushforward i)
      (fun _ : Fin n => I.toSheafOfModules)).symm (hRepeat n)

/-- **The inductive step of [Stacks, Tag 01YF] on an irreducible support.** A coherent module
supported in `T = i(Z)` whose stalk at the generic point is killed by the maximal ideal there is
filtered: [Stacks, Tag 01YE] gives a monomorphism from the direct image of a finite sum of
copies of one coherent ideal sheaf which is an isomorphism near the generic point, so its
cokernel is supported strictly inside `T` and the inductive hypothesis filters it. -/
def integralFiltrationData_of_generic_annihilation
    {X Z : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z))
    (T : Set X) (hT : Set.range i = T)
    (ih : ∀ (G : X.Modules), G.IsCoherent → SheafOfModules.supp G ⊂ T →
      Nonempty (IntegralFiltrationData G))
    (F : X.Modules) [F.IsCoherent] (hF : SheafOfModules.supp F ⊆ T)
    (ha : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal F (i ξ)) :
    IntegralFiltrationData F := by
  classical
  apply Classical.choice
  obtain ⟨r, I, hI, hM, φ, hφ, U, hxU, hU⟩ :=
    Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint
      i ξ hξ F ha
  have hQ : (cokernel φ).IsCoherent :=
    ProperMapping.isCoherent_cokernel hM inferInstance φ
  have hs : SheafOfModules.supp (cokernel φ) ⊂ T := by
    refine supp_ssubset_of_genericPoint_notMem (cokernel φ)
      (hT ▸ isGenericPoint_range_of_isClosedImmersion i hξ) ?_ ?_
    · exact (supp_subset_of_epi (cokernel.π φ) inferInstance).trans hF
    · exact notMem_supp_cokernel_of_isIso_restrict φ U (i ξ) hxU
  obtain ⟨DQ⟩ := ih (cokernel φ) hQ hs
  have DM : IntegralFiltrationData ((Scheme.Modules.pushforward i).obj
      (∐ fun _ : Fin r => I.toSheafOfModules)) := by
    by_cases hnz : IsZero I.toSheafOfModules
    · apply integralFiltrationData_of_isZero
      apply Functor.map_isZero
      apply (IsZero.iff_id_eq_zero _).2
      apply Sigma.hom_ext
      intro j
      exact hnz.eq_of_src _ _
    · exact integralFiltrationData_of_repeated_factor i I hI hnz r
  exact ⟨integralFiltrationData_of_mono_cokernel φ hφ hM inferInstance DM DQ⟩

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
