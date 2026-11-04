module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackPulledBackModule

/-!
# Stacks 02TA for a module pulled back from a third scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `u : A ⟶ B` be a
proper morphism of schemes locally of finite type over `S`, and let both `A` and `B` map to a
third scheme `P` carrying an invertible module `L` with a global section `s`, compatibly with `u`.
Stacks 02TA says that the Gysin map of the pulled-back section on `B` commutes with proper
pushforward along `u`:

  `i_B^* u_* α = j_* i_A^* α`  in  `A_k(Z_B)`,

where `Z_A ⊆ A` and `Z_B ⊆ B` are the zero schemes of the two pullbacks of `s` and `j : Z_A ⟶ Z_B`
is the induced morphism.

`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward` states 02TA with the module
on `A` the pullback along `u` of the module on `B`; here the module on `A` is the pullback along
`A ⟶ P`, which is isomorphic but not equal. The comparison is the one used for the isomorphism
case `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`, which is the special case
where `u` is an isomorphism.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_properPushforward_pullbackModule` — **Stacks 02TA** for a
  module pulled back from a third scheme, at the Gysin system of the first Chern class rule.
* `Stacks.Chow.gysinSystemOfInvertible_properPushforward_pullbackModule_comp` — the same when the
  module on the source is pulled back in two steps, through a fourth scheme.
* `Stacks.Chow.exists_isProper_zeroScheme_pullback_comp_hom` — a morphism of zero schemes over a
  proper `u` exists in that situation, and is proper.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 02TA for a module pulled back from a third scheme.** Let `u : A ⟶ B` be proper over
the base and let `A` and `B` map compatibly to a scheme `P` carrying an invertible module `L` with
a global section `s`. Then the Gysin map of the pullback of `s` to `B` commutes with pushforward
along `u`, the morphism `j` of the two zero schemes being any one over `u`. -/
theorem gysinSystemOfInvertible_properPushforward_pullbackModule (C : ChowSituation.{u})
    {A B P : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (qA : A ⟶ P) (qB : B ⟶ P) (u : A ⟶ B) [IsProper u]
    (hu : u ≫ pB = pA) (huq : u ≫ qB = qA) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback qA).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback qB).obj L)]
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [IsProper j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
    (α : chowGroup C pA (k + 1)) :
    (gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) k
        (properChowPushforward C pA pB u hu (k + 1)
          (properPushforwardDescends C pA pB u hu (k + 1)) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) j hj k
        (properPushforwardDescends C _ _ j hj k)
        ((gysinSystemOfInvertible C).onChow pA ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s) k α) := by
  subst huq
  have := Stacks.ChernCap42.isInvertible_sheafObj_modulePullback
    ((Scheme.Modules.pullback qB).obj L) u
  have hZZ := zeroScheme_pullback_pullback u qB L s
  obtain rfl : j = eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ.symm) ≫
      zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι).1 ?_
    rw [hjsq, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
      subschemeι_eqToHom hZZ.symm]
  refine (gysinSystemOfInvertible_isNaturalUnderProperPushforward C pA pB u hu
    ((Scheme.Modules.pullback qB).obj L) (AlgebraicGeometry.pullbackGlobalSections qB L s) k
    (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    (zeroSchemePullbackHom_subschemeι u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) α).trans ?_
  exact (properChowPushforward_eqToHom_comp_apply_of_heq C pA
    ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) k hZZ.symm
    (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    (zeroSchemeSquare_comp_structureMorphism C pA pB u hu _ _ _
      (zeroSchemePullbackHom_subschemeι u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)))
    hj (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    (heq_gysinHomomorphismOnChowOfInvertible C pA k
      ((Scheme.Modules.pullback (u ≫ qB)).obj L)
      ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback qB).obj L))
      (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s)
      (AlgebraicGeometry.pullbackGlobalSections u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s))
      ((Scheme.Modules.pullbackComp u qB).app L).symm hZZ.symm _ _) α).symm

/-- **Stacks 02TA for a module pulled back in two steps.** Let `u : A ⟶ B` be proper over the
base, let `A ⟶ V ⟶ P` and `B ⟶ P` commute with `u`, and let `L` be invertible on `P` with a global
section `s`. Then the Gysin map of the pullback of `s` to `B` commutes with pushforward along `u`,
the module on `A` being pulled back first to `V` and then to `A`, and the morphism `j` of the two
zero schemes being any one over `u`. -/
theorem gysinSystemOfInvertible_properPushforward_pullbackModule_comp (C : ChowSituation.{u})
    {A B V P : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (a : A ⟶ V) (q : V ⟶ P) (r : B ⟶ P) (u : A ⟶ B) [IsProper u]
    (hu : u ≫ pB = pA) (hur : u ≫ r = a ≫ q) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subscheme ⟶
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subscheme) [IsProper j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι =
      (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) =
      (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
    (α : chowGroup C pA (k + 1)) :
    (gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback r).obj L)
        (AlgebraicGeometry.pullbackGlobalSections r L s) k
        (properChowPushforward C pA pB u hu (k + 1)
          (properPushforwardDescends C pA pB u hu (k + 1)) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) j hj k
        (properPushforwardDescends C _ _ j hj k)
        ((gysinSystemOfInvertible C).onChow pA
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s)) k α) := by
  have hZ := Stacks.Divisors.zeroScheme_pullback_comp a q L s
  have hG := heq_gysinHomomorphismOnChowOfInvertible C pA k
    ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
    ((Scheme.Modules.pullback (a ≫ q)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
      (AlgebraicGeometry.pullbackGlobalSections q L s))
    (AlgebraicGeometry.pullbackGlobalSections (a ≫ q) L s)
    ((Scheme.Modules.pullbackComp a q).app L) hZ
    (gysinOfInvertibleDescends C _ _ _ _) (gysinOfInvertibleDescends C _ _ _ _)
  have hGx := heq_gysin_apply pA k hZ _ _ hG α
  have key : ∀ (Z : A.IdealSheafData)
      (_hZ : Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (a ≫ q)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (a ≫ q) L s) = Z)
      (j : Z.subscheme ⟶ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subscheme) [IsProper j]
      (_hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι = Z.subschemeι ≫ u)
      (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) = Z.subschemeι ≫ pA)
      (y : chowGroup C (Z.subschemeι ≫ pA) k)
      (_hy : y ≍ (gysinSystemOfInvertible C).onChow pA ((Scheme.Modules.pullback (a ≫ q)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (a ≫ q) L s) k α),
      (gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s) k
          (properChowPushforward C pA pB u hu (k + 1)
            (properPushforwardDescends C pA pB u hu (k + 1)) α) =
        properChowPushforward C (Z.subschemeι ≫ pA)
          ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
            (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) j hj k
          (properPushforwardDescends C _ _ j hj k) y := by
    intro Z hZ' j _ hjsq hj y hy
    subst hZ'
    obtain rfl := eq_of_heq hy
    exact gysinSystemOfInvertible_properPushforward_pullbackModule C pA pB (a ≫ q) r u hu hur L s
      k j hjsq hj α
  exact key _ hZ.symm j hjsq hj _ hGx

/-- The zero scheme of a section pulled back in two steps along `A ⟶ V ⟶ P` maps to the zero
scheme of its pullback along `B ⟶ P` over any `u : A ⟶ B` compatible with the two maps to `P`, by a
proper morphism when `u` is proper. -/
theorem exists_isProper_zeroScheme_pullback_comp_hom {A B V P : Scheme.{u}} (a : A ⟶ V)
    (q : V ⟶ P) (r : B ⟶ P) (u : A ⟶ B) [IsProper u] (hur : u ≫ r = a ≫ q) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    ∃ j : (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subscheme ⟶
        (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subscheme,
      IsProper j ∧ j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ u := by
  have hZ : (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))) =
      pullbackZeroScheme u ((Scheme.Modules.pullback r).obj L)
      (AlgebraicGeometry.pullbackGlobalSections r L s) := by
    rw [zeroScheme_pullback_pullback a q L s, pullbackZeroScheme,
      zeroScheme_pullback_pullback u r L s]
    revert hur
    generalize u ≫ r = w
    rintro rfl
    rfl
  refine ⟨eqToHom (congrArg Scheme.IdealSheafData.subscheme hZ) ≫
    zeroSchemePullbackHom u ((Scheme.Modules.pullback r).obj L)
      (AlgebraicGeometry.pullbackGlobalSections r L s), inferInstance, ?_⟩
  rw [Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc, subschemeι_eqToHom hZ]

end Stacks.Chow

end
