module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperBaseChangeAtAPoint

/-!
# The étale-local criterion for base change on higher direct images

Consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

together with an étale covering `{Uᵢ → X}` such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S`
with `Vᵢ → S` étale.  Writing `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, the induced squares

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

are again cartesian.  This file proves the third part of Stacks 0EZR: for an abelian sheaf `F`
on the small étale site of `T` and a degree `q`, if the base change map
`fᵢ^{-1} R^q g_{ᵢ*} Fᵢ ⟶ R^q h_{ᵢ*} eᵢ^{-1} Fᵢ` of each local square is an isomorphism — where
`Fᵢ = F|_{Tᵢ}` is the inverse image of `F` along `Tᵢ ⟶ T` — then so is the base change map
`f^{-1} R^q g_* F ⟶ R^q h_* e^{-1} F` of the outer square.

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_local` — **Stacks 0EZR,
  part (3)**.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v z

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The cancellations of the pasting argument, on variables -/

/-- **Cancellation of invertible factors.**  A fourfold composite `a ≫ b ≫ c ≫ d` is invertible
and all but its second factor are; the second factor is compared with `m` through an identity
`b ≫ α = β ≫ m` whose other two members are invertible; and `m` is compared with `t` through an
identity `p ≫ m = t ≫ s` whose other two members are invertible.  Then `t` is invertible. -/
private lemma isIso_of_paste_cancellation {C : Type*} [Category* C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (α : A₂ ⟶ B₀) (β : A₁ ⟶ B₁) (m : B₁ ⟶ B₀)
    (p : B₂ ⟶ B₁) (t : B₂ ⟶ B₃) (s : B₃ ⟶ B₀)
    [IsIso a] [IsIso c] [IsIso d] [IsIso α] [IsIso β] [IsIso p] [IsIso s]
    (hrect : IsIso (a ≫ b ≫ c ≫ d)) (hnat : b ≫ α = β ≫ m) (hbridge : p ≫ m = t ≫ s) :
    IsIso t := by
  have := hrect
  have : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a (b ≫ c ≫ d)
  have : IsIso b := IsIso.of_isIso_comp_right b (c ≫ d)
  have : IsIso m := IsIso.of_isIso_fac_left hnat.symm
  exact IsIso.of_isIso_fac_right hbridge.symm

/-! ### The base change map of a cartesian square with both inverse-image legs étale

For a cartesian square

```
Y --e--> T
|h       |g
X --f--> S
```

with `f` — hence also `e` — étale, the base change map on abelian small étale sheaves is
invertible, undecorated, derived and in each degree. -/

section EtaleSquare

variable {Y T X S : Scheme.{u}}

/-- **Restriction along an étale morphism preserves injective abelian sheaves**: its left
adjoint is extension by zero, which preserves monomorphisms. -/
private theorem injective_etaleRestriction_obj {U V : Scheme.{u}} (j : U ⟶ V) [Etale j]
    (M : Sheaf (smallEtaleTopology V) AddCommGrpCat.{max (u + 1) v}) (hM : Injective M) :
    Injective ((etaleRestriction.{u, v} j).obj M) :=
  (extensionByZeroAdj.{u, v} j).map_injective M hM

/-- **Restriction along an étale morphism is left adjoint to the direct image**, on abelian
sheaves: the adjunction induced on sheaves by the site-level adjunction
`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj`. -/
private def smallEtaleRestrictionAdjunctionAb {U V : Scheme.{u}} (j : U ⟶ V) [Etale j] :
    etaleRestrictionAt j Ab.{u + 1} ⊣ smallEtalePushforwardAb j :=
  (smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
    (smallEtaleTopology U) (smallEtaleTopology V)

/-- **The inverse image of an injective abelian sheaf along an étale morphism is injective.**
For `e` étale the inverse image and the restriction are two left adjoints of the same direct
image, hence isomorphic, and the restriction preserves injective objects by
`injective_etaleRestriction_obj`. -/
private theorem injective_smallEtalePullbackAb_obj (e : Y ⟶ T) [Etale e]
    (M : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (hM : Injective M) :
    Injective ((smallEtalePullbackAb e).obj M) :=
  Injective.of_iso
    (((smallEtaleAdjunctionAb e).leftAdjointUniq
      (smallEtaleRestrictionAdjunctionAb e)).app M).symm
    (injective_etaleRestriction_obj.{u, u + 1} e M hM)

/-- **An injective object is right acyclic for an additive functor**,
`CategoryTheory.Functor.rightAcyclic_of_injective` with the injectivity taken as a hypothesis
rather than as an instance. -/
private theorem rightAcyclic_of_injective {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (M : A) (hM : Injective M) : F.rightAcyclic M :=
  have := hM
  CategoryTheory.Functor.rightAcyclic_of_injective F M

/-- The square comparison of direct images at arbitrary coefficients, instantiated at the abelian
coefficients `Ab.{u + 1}`, is the comparison whose mate
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is.  Both are the composite of the two
comparisons of composite direct images through the common diagonal, so only the bookkeeping of
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_eq` separates them. -/
private lemma smallEtaleSquarePushforwardIsoAt_eq {X' Y S T : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) :
    smallEtaleSquarePushforwardIsoAt e h g f' w.symm Ab.{u + 1} =
      smallEtaleSquarePushforwardIso f' g h e w :=
  Eq.trans
    (show smallEtaleSquarePushforwardIsoAt e h g f' w.symm Ab.{u + 1} =
        (smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm) from rfl)
    (smallEtaleSquarePushforwardIso_eq f' g h e w).symm

/-- **The underived base change map of a cartesian square with both inverse-image legs étale is
invertible.**  This is
`Stacks.EtaleCohomology.isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback` at the abelian
coefficients `Ab.{u + 1}` and the two inverse-image/direct-image adjunctions, read in the
vocabulary of `Stacks.EtaleCohomology.smallEtaleBaseChangeAb`. -/
private theorem isIso_smallEtaleBaseChangeAb_of_isPullback (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S)
    (f : X ⟶ S) (w : h ≫ f = e ≫ g) (sq : IsPullback e h g f) [Etale e] [Etale f] :
    IsIso (smallEtaleBaseChangeAb f g h e w) := by
  have (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
      IsIso ((smallEtaleBaseChangeAb f g h e w).app F) := by
    rw [smallEtaleBaseChangeAb_eq_mate, Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm,
      ← smallEtaleSquarePushforwardIsoAt_eq f g h e w]
    exact isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback Ab.{u + 1} e h g f w.symm sq
      (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f) F
  exact NatIso.isIso_of_isIso_app _

/-- **The derived base change comparison of a cartesian square with both inverse-image legs étale
is invertible.**  The underived comparison is invertible, the inverse image of abelian étale
sheaves is exact, and the inverse image of an injective sheaf is right acyclic for the direct
image; `Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived` then computes both derived
functors on a complex of injectives, where the comparison is degreewise. -/
private theorem isIso_smallEtaleDerivedBaseChangeAb_of_isPullback (e : Y ⟶ T) (h : Y ⟶ X)
    (g : T ⟶ S) (f : X ⟶ S) (w : h ≫ f = e ≫ g) (sq : IsPullback e h g f)
    [Etale e] [Etale f] :
    IsIso (smallEtaleDerivedBaseChangeAb f g h e w) := by
  have := isIso_smallEtaleBaseChangeAb_of_isPullback e h g f w sq
  have : IsIso (smallEtalePullbackAb e).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb e)
  have : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb f)
  exact Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived
    (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
    (smallEtalePullbackAb f) (smallEtalePullbackAb e)
    (smallEtaleBaseChangeAb f g h e w)
    (fun M _ => inferInstance)
    (asIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith)
    fun M hM => rightAcyclic_of_injective (smallEtalePushforwardAb h) _
      (injective_smallEtalePullbackAb_obj e M hM)

/-- **The degree-`q` base change map of a cartesian square with both inverse-image legs étale is
invertible.**  The degree-`q` map is the degree-`q` cohomology of the derived comparison, which
is invertible by `isIso_smallEtaleDerivedBaseChangeAb_of_isPullback`. -/
private theorem isIso_higherBaseChangeMapAb_app_of_isPullback (e : Y ⟶ T) (h : Y ⟶ X)
    (g : T ⟶ S) (f : X ⟶ S) (w : h ≫ f = e ≫ g) (sq : IsPullback e h g f)
    [Etale e] [Etale f] (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f g h e w q).app G) := by
  have := isIso_smallEtaleDerivedBaseChangeAb_of_isPullback e h g f w sq
  rw [isIso_higherBaseChangeMapAb_app_iff]
  infer_instance

end EtaleSquare

/-! ### The two decompositions of the rectangle -/

section Rectangle

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}

/-- **Transport of the degree-`q` base change map along equalities of the two vertical legs.**
The two commutativity proofs are interchangeable by proof irrelevance, so only the two equalities
of morphisms are needed. -/
private lemma isIso_higherBaseChangeMapAb_app_congr {X' S T Y : Scheme.{u}} {f₁ f₂ : X' ⟶ S}
    (hf : f₁ = f₂) (g : T ⟶ S) (h : Y ⟶ X') {e₁ e₂ : Y ⟶ T} (he : e₁ = e₂)
    {w₁ : h ≫ f₁ = e₁ ≫ g} {w₂ : h ≫ f₂ = e₂ ≫ g} (q : ℕ)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hiso : IsIso ((higherBaseChangeMapAb f₁ g h e₁ w₁ q).app G)) :
    IsIso ((higherBaseChangeMapAb f₂ g h e₂ w₂ q).app G) := by
  subst hf
  subst he
  exact hiso

/-- **The pasting law for the degree-`q` base change map, run backwards.**  For two horizontally
composable commutative squares, if the derived base change comparison of the upper square is
invertible and the degree-`q` base change map of the outer rectangle is invertible at `F`, then
the inverse image along `u₂` of the degree-`q` base change map of the lower square is invertible
at `F`.  This is the direction opposite to
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste`. -/
private theorem isIso_pullback_map_higherBaseChangeMapAb_app_of_paste (g₀ : X₀ ⟶ S₀)
    (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂) (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1})
    (hupper : IsIso (smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂))
    (hrect : IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F)) :
    IsIso ((smallEtalePullbackAb u₂).map
      ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F)) := by
  have := hupper
  rw [isIso_higherBaseChangeMapAb_app_iff,
    smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂] at hrect
  simp only [Functor.map_comp] at hrect
  have hnat := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb u₂) (q : ℤ)).hom.naturality
    ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hbridge := congrArg (smallEtalePullbackAb u₂).map
    (baseChangeSourceIso_hom_app_comp u₁ g₀ g₁ v₁ w₁ q F)
  simp only [Functor.map_comp] at hbridge
  exact isIso_of_paste_cancellation _ _ _ _ _ _ _ _ _ _ hrect hnat hbridge

end Rectangle

/-! ### Stacks 0EZR, part (3) -/

/-- **Stacks 0EZR, part (3).**  Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S`
factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, let `F` be an abelian sheaf on the small étale site
of `T` and let `q` be a degree.  If for every `i` the base change map on higher direct images
`fᵢ^{-1} R^q g_{ᵢ*} Fᵢ ⟶ R^q h_{ᵢ*} eᵢ^{-1} Fᵢ` of the `i`-th local square is an isomorphism,
where `Fᵢ = F|_{Vᵢ ×_S T}` is the inverse image of `F` along `Tᵢ ⟶ T`, then the base change map
`f^{-1} R^q g_* F ⟶ R^q h_* e^{-1} F` of the outer square is an isomorphism.

Each degree is a separate statement, with the same degree in the hypothesis and in the
conclusion, and no finiteness, separatedness or torsion condition enters. -/
theorem isIso_higherBaseChangeMapAb_app_of_isIso_local
    (D : EtaleLocalBaseChangeData.{u, z, _, _} Ab.{u + 1}) (q : ℕ)
    (hlocal : ∀ i : D.I,
      IsIso ((higherBaseChangeMapAb (D.f_i i) (D.g_i i) (D.h_i i) (D.e_i i)
        (D.local_cartesian i).w q).app ((smallEtalePullbackAb (D.toT_i i)).obj D.F))) :
    IsIso ((higherBaseChangeMapAb D.f D.g D.h D.e D.cartesian.w q).app D.F) := by
  have hEt : ∀ i, Etale (D.u i) := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp D.cover).2
  have (i : D.I) : Etale (D.u i) := hEt i
  refine isIso_of_isIso_etaleRestrictionAt _ D.u
    (coversTop_smallEtaleObj_cover D hEt) fun i => ?_
  have : Etale (D.v i) := D.etale_v i
  have : Etale (D.toY_i i) := Etale.etale_of_isPullback_snd (D.upper_cartesian i)
  have : Etale (D.toT_i i) := Etale.etale_of_isPullback_snd (D.lower_cartesian i)
  have hlower : IsIso ((higherBaseChangeMapAb (D.v i) D.g (D.g_i i) (D.toT_i i)
      (D.lower_cartesian i).w q).app D.F) :=
    isIso_higherBaseChangeMapAb_app_of_isPullback (D.toT_i i) (D.g_i i) D.g (D.v i)
      (D.lower_cartesian i).w (D.lower_cartesian i).flip q D.F
  have hupper : IsIso (smallEtaleDerivedBaseChangeAb (D.u i) D.h (D.h_i i) (D.toY_i i)
      (D.upper_cartesian i).w) :=
    isIso_smallEtaleDerivedBaseChangeAb_of_isPullback (D.toY_i i) (D.h_i i) D.h (D.u i)
      (D.upper_cartesian i).w (D.upper_cartesian i).flip
  have hrect₀ := isIso_higherBaseChangeMapAb_app_of_paste D.g (D.g_i i) (D.h_i i) (D.v i)
    (D.f_i i) (D.toT_i i) (D.e_i i) (D.lower_cartesian i).w (D.local_cartesian i).w q D.F
    hlower (hlocal i)
  have hrect : IsIso ((higherBaseChangeMapAb (D.u i ≫ D.f) D.g (D.h_i i) (D.toY_i i ≫ D.e)
      (smallEtaleRectangle_comm D.g D.h (D.h_i i) D.f (D.u i) D.e (D.toY_i i)
        D.cartesian.w (D.upper_cartesian i).w) q).app D.F) :=
    isIso_higherBaseChangeMapAb_app_congr (D.factorization i) D.g (D.h_i i)
      (D.e_i_compatible i) q D.F hrect₀
  refine (NatIso.isIso_map_iff
    ((smallEtaleAdjunctionAb (D.u i)).leftAdjointUniq
      (smallEtaleRestrictionAdjunctionAb (D.u i))) _).mp ?_
  exact isIso_pullback_map_higherBaseChangeMapAb_app_of_paste D.g D.h (D.h_i i) D.f (D.u i)
    D.e (D.toY_i i) D.cartesian.w (D.upper_cartesian i).w q D.F hupper hrect

end Stacks.EtaleCohomology

end
