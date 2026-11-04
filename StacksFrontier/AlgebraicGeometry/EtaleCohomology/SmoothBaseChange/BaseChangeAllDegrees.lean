module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules

/-!
# Base change in every degree

For a morphism of schemes `f : X ⟶ S` and an integer `n`, the condition `BC(f, n, q)` of
Stacks, Remark 0F02 asks that the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` be an
isomorphism for every diagram of two cartesian squares over `f`, every quasi-compact and
quasi-separated `g` and every abelian sheaf `F` annihilated by `n`, in degrees up to `q`. This
file studies the condition in every degree at once, `BaseChangeAllDegrees f n`. It records the
formal properties the second proof of the smooth base change theorem (Stacks, Theorem 0EYU) uses:

* it only depends on `f` up to isomorphism of its source;
* it is stable under composition, by Stacks 0EZS;
* it is étale local on the source and the target, by Stacks 0EZR;
* every étale morphism satisfies it, by Stacks 0EZR applied to the covering of `X` by itself,
  whose local square is an identity square.

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees` — `BC(f, n, q)` for every `q`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees.comp` — composition.
* `Stacks.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees.of_etaleCover` — étale
  locality.
* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale` — base change
  along an étale morphism.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- `BC(f, n, q)` of Stacks, Remark 0F02, for every degree `q`. -/
def BaseChangeAllDegrees {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) : Prop :=
  ∀ q₀ : ℤ, BaseChangeHolds f n q₀

/-- `BC(f, n, q)` in every degree, in the form it is used: the base change map of every diagram
of two cartesian squares over `f` is an isomorphism in every degree at every sheaf annihilated by
`n`. -/
theorem BaseChangeAllDegrees.isIso {X S : Scheme.{u}} {f : X ⟶ S} {n : ℤ}
    (H : BaseChangeAllDegrees f n) {S' X' T Y : Scheme.{u}} (s : S' ⟶ S) (p : X' ⟶ X)
    (f' : X' ⟶ S') (hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app F) :=
  H q s p f' hp g h e sq F hF q le_rfl

/-- `BC(f, n, q)` in every degree follows from the statement in every degree `q : ℕ`. -/
theorem BaseChangeAllDegrees.of_isIso {X S : Scheme.{u}} {f : X ⟶ S} {n : ℤ}
    (H : ∀ {S' X' T Y : Scheme.{u}} (s : S' ⟶ S) (p : X' ⟶ X)
      (f' : X' ⟶ S') (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
      (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
      (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      (∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) → ∀ q : ℕ,
      IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app F)) :
    BaseChangeAllDegrees f n :=
  fun _ _ _ _ _ s p f' hp g h e sq _ _ F hF q _ => H s p f' hp g h e sq F hF q

/-- Invertibility of the base change map on higher direct images depends on the morphisms of the
square only through their values. -/
theorem isIso_higherBaseChangeMapAb_congr {X' Y S T : Scheme.{u}} {f₁ f₂ : X' ⟶ S}
    {g₁ g₂ : T ⟶ S} {h₁ h₂ : Y ⟶ X'} {e₁ e₂ : Y ⟶ T} (hf : f₁ = f₂) (hg : g₁ = g₂)
    (hh : h₁ = h₂) (he : e₁ = e₂) (w₁ : h₁ ≫ f₁ = e₁ ≫ g₁) (w₂ : h₂ ≫ f₂ = e₂ ≫ g₂) (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f₁ g₁ h₁ e₁ w₁ q).app F) ↔
      IsIso ((higherBaseChangeMapAb f₂ g₂ h₂ e₂ w₂ q).app F) := by
  subst hf hg hh he
  rfl

/-- Inverse image of abelian sheaves on the small étale sites preserves annihilation by `n`. -/
theorem zsmul_pullbackAb_eq_zero {T T' : Scheme.{u}} (e : T' ⟶ T)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (n : ℤ)
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) (U : T'.Etale)
    (x : ((smallEtalePullbackAb e).obj F).obj.obj (Opposite.op U)) : n • x = 0 := by
  have h0 : n • 𝟙 F = 0 :=
    (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F n).2 fun U x => hF U.unop x
  have h1 : n • 𝟙 ((smallEtalePullbackAb e).obj F) = 0 := by
    have h := congrArg (smallEtalePullbackAb e).map h0
    rwa [Functor.map_zsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).1 h1 (Opposite.op U) x

/-! ### Isomorphism of the source -/

/-- `BC(f, n, q)` in every degree depends on `f` only up to an isomorphism of its source. -/
theorem BaseChangeAllDegrees.of_iso {X₀ X S : Scheme.{u}} (i : X₀ ≅ X) {f : X ⟶ S} {n : ℤ}
    (H : BaseChangeAllDegrees f n) : BaseChangeAllDegrees (i.hom ≫ f) n := by
  refine BaseChangeAllDegrees.of_isIso fun s p f' hp g h e sq _ _ F hF q => ?_
  have hi : IsPullback i.hom (i.hom ≫ f) f (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hp' : IsPullback (p ≫ i.hom) f' f s := by
    simpa using hp.paste_horiz hi
  exact H.isIso s (p ≫ i.hom) f' hp' g h e sq F hF q

/-! ### Composition -/

/-- **`BC(f, n, q)` in every degree is stable under composition** (Stacks 0EZS). If `f₁ : X ⟶ S`
and `f₂ : W ⟶ X` satisfy it, so does `f₂ ≫ f₁`. A diagram over `f₂ ≫ f₁` is split along the base
change `X' = X ×_S S'` into a diagram over `f₁` and a diagram over `f₂`, and the base change map
of the outer rectangle is invertible because the two maps it is pasted from are. -/
theorem BaseChangeAllDegrees.comp (h0EZS : HigherBaseChangePaste.{u}) {W X S : Scheme.{u}}
    {f₂ : W ⟶ X} {f₁ : X ⟶ S} {n : ℤ} (H₂ : BaseChangeAllDegrees f₂ n)
    (H₁ : BaseChangeAllDegrees f₁ n) : BaseChangeAllDegrees (f₂ ≫ f₁) n := by
  refine BaseChangeAllDegrees.of_isIso fun {S' W' T Y} s p f' hp g h e sq _ _ F hF q => ?_
  have hp₁ : IsPullback (pullback.fst f₁ s) (pullback.snd f₁ s) f₁ s :=
    IsPullback.of_hasPullback f₁ s
  let f₂' : W' ⟶ pullback f₁ s := pullback.lift (p ≫ f₂) f' (by
    rw [Category.assoc, hp.w])
  have hf₂'₂ : f₂' ≫ pullback.snd f₁ s = f' := pullback.lift_snd _ _ _
  have hp₂ : IsPullback p f₂' f₂ (pullback.fst f₁ s) :=
    IsPullback.of_bot (by rwa [hf₂'₂]) (pullback.lift_fst _ _ _).symm hp₁
  have sq₁ : IsPullback (pullback.fst (pullback.snd f₁ s) g)
      (pullback.snd (pullback.snd f₁ s) g) (pullback.snd f₁ s) g :=
    IsPullback.of_hasPullback _ _
  let k : Y ⟶ pullback (pullback.snd f₁ s) g := pullback.lift (h ≫ f₂') e (by
    rw [Category.assoc, hf₂'₂, sq.w])
  have hk₂ : k ≫ pullback.snd (pullback.snd f₁ s) g = e := pullback.lift_snd _ _ _
  have sq₂ : IsPullback h k f₂' (pullback.fst (pullback.snd f₁ s) g) :=
    IsPullback.of_bot (by rwa [hk₂, hf₂'₂]) (pullback.lift_fst _ _ _).symm sq₁
  have i₁ := H₁.isIso s (pullback.fst f₁ s) (pullback.snd f₁ s) hp₁ g _ _ sq₁ F hF q
  have i₂ := H₂.isIso (pullback.fst f₁ s) p f₂' hp₂ (pullback.fst (pullback.snd f₁ s) g) h k
    sq₂ ((smallEtalePullbackAb (pullback.snd (pullback.snd f₁ s) g)).obj F)
    (zsmul_pullbackAb_eq_zero _ F n hF) q
  exact (isIso_higherBaseChangeMapAb_congr hf₂'₂ rfl rfl hk₂ _ _ q F).1
    (h0EZS g (pullback.fst (pullback.snd f₁ s) g) h (pullback.snd f₁ s) f₂'
      (pullback.snd (pullback.snd f₁ s) g) k sq₁.w sq₂.w q F i₁ i₂)

/-! ### The identity square and étale morphisms -/

/-- **The base change map of a square whose vertical morphism and right vertical morphism are
identities is invertible**, in every degree: its derived comparison is the composite of the two
comparisons of the inverse images along the identities with the identity functor. -/
theorem isIso_higherBaseChangeMapAb_id {X Y : Scheme.{u}} (h : Y ⟶ X) (w : h ≫ 𝟙 X = 𝟙 Y ≫ h)
    (q : ℕ) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb (𝟙 X) h h (𝟙 Y) w q).app F) := by
  refine isIso_higherBaseChangeMapAb_app_of_isIso_derived _ _ _ _ w F ?_ q
  rw [smallEtaleDerivedBaseChangeAb_id_app h (𝟙 X) (𝟙 Y) rfl rfl w]
  infer_instance

/-- **Base change along an étale morphism** (Stacks 0EZR, applied to the covering of `X` by
itself). In a cartesian square whose left vertical morphism `f` is étale, the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for every abelian sheaf `F` and every `q`:
`f` factors as `𝟙 X` followed by the étale `f`, and the local square of that factorization is a
square with identity vertical morphisms. -/
theorem isIso_higherBaseChangeMapAb_of_etale (h0EZR : EtaleLocalHigherBaseChange.{u})
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Etale f] (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (q : ℕ) : IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) := by
  let D : EtaleLocalBaseChangeData.{u, u} Ab.{u + 1} :=
    { X := X, Y := Y, S := S, T := T, f := f, h := h, e := e, g := g, cartesian := sq
      I := PUnit, U := fun _ => X, u := fun _ => 𝟙 X
      cover := ofArrows_mem_etalePrecoverage_iff.2
          ⟨fun x => ⟨PUnit.unit, x, rfl⟩, fun _ => inferInstance⟩
      V := fun _ => X, v := fun _ => f, etale_v := fun _ => inferInstance
      f_i := fun _ => 𝟙 X, factorization := fun _ => rfl
      Y_i := fun _ => Y, h_i := fun _ => h, toY_i := fun _ => 𝟙 Y
      upper_cartesian := fun _ => IsPullback.id_vert h
      T_i := fun _ => Y, g_i := fun _ => h, toT_i := fun _ => e
      lower_cartesian := fun _ => sq
      e_i := fun _ => 𝟙 Y, e_i_compatible := fun _ => rfl
      local_cartesian := fun _ => IsPullback.id_vert h
      F := F }
  exact h0EZR D q fun _ => isIso_higherBaseChangeMapAb_id h _ q _

/-- **An étale morphism satisfies `BC(f, n, q)` in every degree**: every base change of an étale
morphism is étale. -/
theorem baseChangeAllDegrees_of_etale (h0EZR : EtaleLocalHigherBaseChange.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (n : ℤ) : BaseChangeAllDegrees f n := by
  refine BaseChangeAllDegrees.of_isIso fun s p f' hp g h e sq _ _ F _ q => ?_
  have : Etale f' := MorphismProperty.of_isPullback hp ‹Etale f›
  exact isIso_higherBaseChangeMapAb_of_etale h0EZR f' h e g sq F q

/-! ### Étale locality -/

section EtaleCover

variable {X S X' S' Y T : Scheme.{u}} {f : X ⟶ S} {ι : Type u} {U V : ι → Scheme.{u}}
  {u : ∀ i, U i ⟶ X} {v : ∀ i, V i ⟶ S} (fᵢ : ∀ i, U i ⟶ V i)
  (hfac : ∀ i, fᵢ i ≫ v i = u i ≫ f) {s : S' ⟶ S} {p : X' ⟶ X} {f' : X' ⟶ S'}
  (hp : IsPullback p f' f s) {g : T ⟶ S'} {h : Y ⟶ X'} {e : Y ⟶ T} (sq : IsPullback h e f' g)

include hfac hp in
/-- The base change `Uᵢ ×_X X' ⟶ Vᵢ ×_S S'` of a factorization `uᵢ ≫ f = fᵢ ≫ vᵢ` along a base
change `X' = X ×_S S'`. -/
def baseChangedFactorization (i : ι) : pullback (u i) p ⟶ pullback (v i) s :=
  pullback.lift (pullback.fst (u i) p ≫ fᵢ i) (pullback.snd (u i) p ≫ f') (by
    rw [Category.assoc, hfac, ← Category.assoc, pullback.condition, Category.assoc, hp.w,
      Category.assoc])

/-- The first projection of `baseChangedFactorization` is `pullback.fst (u i) p ≫ fᵢ i`. -/
theorem baseChangedFactorization_fst (i : ι) :
    baseChangedFactorization fᵢ hfac hp i ≫ pullback.fst (v i) s =
      pullback.fst (u i) p ≫ fᵢ i :=
  pullback.lift_fst _ _ _

/-- The second projection of `baseChangedFactorization` is `pullback.snd (u i) p ≫ f'`. -/
theorem baseChangedFactorization_snd (i : ι) :
    baseChangedFactorization fᵢ hfac hp i ≫ pullback.snd (v i) s =
      pullback.snd (u i) p ≫ f' :=
  pullback.lift_snd _ _ _

/-- The base changed factorization is the base change of `fᵢ`:
`Uᵢ ×_X X' = Uᵢ ×_{Vᵢ} Vᵢ ×_S S'`. -/
theorem isPullback_baseChangedFactorization (i : ι) :
    IsPullback (pullback.fst (u i) p) (baseChangedFactorization fᵢ hfac hp i) (fᵢ i)
      (pullback.fst (v i) s) := by
  have hout : IsPullback (pullback.fst (u i) p)
      (baseChangedFactorization fᵢ hfac hp i ≫ pullback.snd (v i) s) (fᵢ i ≫ v i) s := by
    rw [baseChangedFactorization_snd, hfac]
    exact (IsPullback.of_hasPullback (u i) p).paste_vert hp
  exact IsPullback.of_bot hout (baseChangedFactorization_fst fᵢ hfac hp i).symm
    (IsPullback.of_hasPullback (v i) s)

/-- The diagonal `Uᵢ ×_X Y ⟶ (Vᵢ ×_S S') ×_{S'} T` of the `i`-th local square of Stacks 0EZR. -/
def localSquareDiagonal (i : ι) :
    pullback (pullback.snd (u i) p) h ⟶ pullback (pullback.snd (v i) s) g :=
  pullback.lift (pullback.fst (pullback.snd (u i) p) h ≫ baseChangedFactorization fᵢ hfac hp i)
    (pullback.snd (pullback.snd (u i) p) h ≫ e) (by
      rw [Category.assoc, baseChangedFactorization_snd, ← Category.assoc, pullback.condition,
        Category.assoc, sq.w, Category.assoc])

/-- The `i`-th local square of Stacks 0EZR is cartesian. -/
theorem isPullback_localSquare (i : ι) :
    IsPullback (pullback.fst (pullback.snd (u i) p) h) (localSquareDiagonal fᵢ hfac hp sq i)
      (baseChangedFactorization fᵢ hfac hp i) (pullback.fst (pullback.snd (v i) s) g) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback (pullback.snd (v i) s) g)
  rw [localSquareDiagonal, pullback.lift_snd, baseChangedFactorization_snd]
  exact (IsPullback.of_hasPullback (pullback.snd (u i) p) h).paste_vert sq

end EtaleCover

/-- **`BC(f, n, q)` in every degree is étale local** (Stacks 0EZR). Let `{uᵢ : Uᵢ ⟶ X}` be an
étale covering such that each `uᵢ ≫ f` factors as `fᵢ ≫ vᵢ` with `vᵢ : Vᵢ ⟶ S` étale. If every
`fᵢ` satisfies `BC(fᵢ, n, q)` in every degree, so does `f`. Over a base change `S' ⟶ S` the
covering and the factorizations base change, and each local square of Stacks 0EZR is a diagram
over `fᵢ`. -/
theorem BaseChangeAllDegrees.of_etaleCover (h0EZR : EtaleLocalHigherBaseChange.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {ι : Type u} (U V : ι → Scheme.{u})
    (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ S) (fᵢ : ∀ i, U i ⟶ V i)
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (u i)) [∀ i, Etale (u i)] [∀ i, Etale (v i)]
    (hfac : ∀ i, fᵢ i ≫ v i = u i ≫ f) (H : ∀ i, BaseChangeAllDegrees (fᵢ i) n) :
    BaseChangeAllDegrees f n := by
  refine BaseChangeAllDegrees.of_isIso fun {S' X' T Y} s p f' hp g h e sq _ _ F hF q => ?_
  have hcov' : Presieve.ofArrows (fun i => pullback (u i) p) (fun i => pullback.snd (u i) p) ∈
      Scheme.etalePrecoverage X' := by
    refine ofArrows_mem_etalePrecoverage_iff.2 ⟨fun x => ?_, fun _ => inferInstance⟩
    obtain ⟨i, y, hy⟩ := hcov (p x)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz⟩
  let D : EtaleLocalBaseChangeData.{u, u} Ab.{u + 1} :=
    { X := X', Y := Y, S := S', T := T, f := f', h := h, e := e, g := g, cartesian := sq
      I := ι, U := fun i => pullback (u i) p, u := fun i => pullback.snd (u i) p
      cover := hcov'
      V := fun i => pullback (v i) s, v := fun i => pullback.snd (v i) s
      etale_v := fun _ => inferInstance
      f_i := baseChangedFactorization fᵢ hfac hp
      factorization := baseChangedFactorization_snd fᵢ hfac hp
      Y_i := fun i => pullback (pullback.snd (u i) p) h
      h_i := fun i => pullback.fst (pullback.snd (u i) p) h
      toY_i := fun i => pullback.snd (pullback.snd (u i) p) h
      upper_cartesian := fun i => IsPullback.of_hasPullback _ _
      T_i := fun i => pullback (pullback.snd (v i) s) g
      g_i := fun i => pullback.fst (pullback.snd (v i) s) g
      toT_i := fun i => pullback.snd (pullback.snd (v i) s) g
      lower_cartesian := fun i => IsPullback.of_hasPullback _ _
      e_i := localSquareDiagonal fᵢ hfac hp sq
      e_i_compatible := fun i => pullback.lift_snd _ _ _
      local_cartesian := isPullback_localSquare fᵢ hfac hp sq
      F := F }
  exact h0EZR D q fun i => (H i).isIso (pullback.fst (v i) s) (pullback.fst (u i) p)
    (baseChangedFactorization fᵢ hfac hp i) (isPullback_baseChangedFactorization fᵢ hfac hp i)
    _ _ _ (isPullback_localSquare fᵢ hfac hp sq i) _ (zsmul_pullbackAb_eq_zero _ F n hF) q

end Stacks.EtaleCohomology.SmoothBaseChange

end
