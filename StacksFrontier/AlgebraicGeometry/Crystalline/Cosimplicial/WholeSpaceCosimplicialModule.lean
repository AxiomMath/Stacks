module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamColumnZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsPAdicComplete

/-!
# The cosimplicial module `M(•)` of a general crystal over the completed cosimplicial envelope

The double complex of the proof of [Stacks, Proposition 60.21.3, Tag 07LG] is

`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`,

and `Crystalline.CosimplicialCompletedPair.doubleComplex` builds it from a
`Crystalline.CosimplicialCompletedModule` — a module over the completed cosimplicial rings `D̂(*)`
in each cosimplicial degree, with semilinear transitions — together with a connection in each
degree.

This file constructs the cosimplicial module for an arbitrary crystal `ℱ` in quasi-coherent
`𝒪_{X/S}`-modules, over the cosimplicial envelope of the situation: in cosimplicial degree `b` it
is the module

`M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)`

of [Stacks, Proposition 60.20.1, Tag 07JN], with the restriction maps of `ℱ` along the transition
maps of `wholeSpaceSystem` as its transitions.

## Main definitions

* `wholeSpaceSections`: the module `M(n)` of the cosimplicial degree `n`, a module over `D̂(n)`.
* `wholeSpaceSectionsTrans`: the semilinear cosimplicial transition `M(m) → M(n)`.
* `wholeSpaceCosimplicialModule`: the cosimplicial module `M(•)` of a quasi-coherent crystal, as
  a `Crystalline.CosimplicialCompletedModule`.
* `wholeSpaceColumnZeroIso`: the column `a = 0` of the double complex of a quasi-coherent crystal
  is isomorphic to `M(•)`.
* `wholeSpaceMooreHomologyColumnZeroIso`: the cohomology of the Moore complex of the column
  `a = 0` is the cohomology of the Moore complex of `M(•)`.

## Main results

* `Crystalline.isAdicComplete_map_of_ringEquiv`: adic completeness is preserved by a change of
  scalars along a ring isomorphism.
* `wholeSpaceSectionsVal_smul`: a scalar of `D̂(n)` acts on `M(n)` level by level, through
  `levelSectionsScalars`.
* `wholeSpaceSectionsIsAdicComplete`: each `M(n)` is `p`-adically complete over `D̂(n)`.

## Implementation notes

The carrier is the limit of sections and not a base change `D̂(b) ⊗̂_{D̂} M`. The two differ, and
only the first makes the column `a = 0` of `K` the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Tag 07JN]: with a base-change carrier the column `a = 0` is the constant cosimplicial
group, whose Moore complex has zero differential.

The completed ring of the cosimplicial degree `b` of `Crystalline.envelopeDPAlgebra` at the
tautological presentation is, by `rfl`, the degree `b` of `wholeSpaceEnvelopeRing`, and its
transition maps are the structure maps of that cosimplicial ring
(`wholeSpaceDPAlgebra_completedRing`, `wholeSpaceDPAlgebra_completedRingMap`). The sections over a
single level `(b, e)` are a module over that ring by `levelSectionsScalars`, and
`levelSectionsScalars_restriction` is the semilinearity in the cosimplicial direction.

The `p`-adic completeness of `M(b)` is item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG], namely
`isPAdicallyComplete_wholeSpaceLevelScalars_sections`, transported along the change of scalars by
`Crystalline.isAdicComplete_map_of_ringEquiv`.

The connection in each cosimplicial degree is not constructed here.

## What this does and does not do to [Stacks, Tag 07LG]

**No `@[stacks …]` attribute is placed.** [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`. What falls here is the module half of the double
complex `K` for a general crystal; the connection in each cosimplicial degree is not built here, so
no `Crystalline.CosimplicialCompletedPair` follows from this module alone: the pair of a general
crystal is `...SmallSite.crystalCosimplicialPair` of `SmallSite/CrystalCosimplicialPair.lean`. The
remaining hypotheses of `...SmallSite.computes07LG_of_doubleComplexSmall_of_edges` (the acyclicity
of the columns, the rowwise comparison and its quasi-isomorphy, and the two edge identifications)
are untouched.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

namespace Crystalline

/-! ### Adic completeness through a change of scalars along a ring isomorphism -/

section AdicCompleteTransport

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] (f : R ≃+* R')
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M]
  (hsmul : ∀ (a : R) (x : M), (f a) • x = a • x)

include hsmul

/-- **The two filtrations of `M` by the powers of an ideal and of its image agree**, when the two
module structures are related by a ring isomorphism `f` as in `hsmul`. -/
theorem mem_pow_smul_top_map_iff (I : Ideal R) (k : ℕ) (y : M) :
    y ∈ (I.map (f : R →+* R')) ^ k • (⊤ : Submodule R' M) ↔
      y ∈ I ^ k • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow]
  generalize I ^ k = J
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · refine Submodule.smul_induction_on hy (fun a ha x _ ↦ ?_) (fun _ _ ↦ add_mem)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : R →+* R') f.surjective).1 ha
    exact hsmul b x ▸ Submodule.smul_mem_smul hb Submodule.mem_top
  · refine Submodule.smul_induction_on hy (fun a ha x _ ↦ ?_) (fun _ _ ↦ add_mem)
    exact hsmul a x ▸ Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

/-- **Adic completeness survives a change of scalars along a ring isomorphism.**  If `M` is
`I`-adically complete over `R` and the `R'`-action is the `R`-action through `f`, then `M` is
`f(I)`-adically complete over `R'`. -/
theorem isAdicComplete_map_of_ringEquiv (I : Ideal R) [IsAdicComplete I M] :
    IsAdicComplete (I.map (f : R →+* R')) M := by
  have key (k : ℕ) (x y : M) : x ≡ y [SMOD (I.map (f : R →+* R')) ^ k • (⊤ : Submodule R' M)] ↔
      x ≡ y [SMOD I ^ k • (⊤ : Submodule R M)] := by
    simp only [SModEq.sub_mem, mem_pow_smul_top_map_iff f hsmul]
  exact { toIsHausdorff := ⟨fun x hx ↦ IsHausdorff.haus (inferInstance : IsHausdorff I M) x fun k ↦
            (key k _ _).1 (hx k)⟩
          toIsPrecomplete := ⟨fun a ha ↦
            (IsPrecomplete.prec' (I := I) (M := M) a fun {m n} hmn ↦ (key m _ _).1 (ha hmn)).imp
              fun L hL k ↦ (key k _ _).2 (hL k)⟩ }

end AdicCompleteTransport

namespace GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The cosimplicial divided power algebra `D(*)` of the situation's own presentation.** -/
abbrev wholeSpaceDPAlgebra : CosimplicialDPAlgebra.{u, u} ((affineSituation S hp).A : Type u) :=
  envelopeDPAlgebra (affineSituation S hp) (wholeSpacePresentation S hp)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The completed ring of the cosimplicial degree `n` is the degree `n` of
`...SmallSite.wholeSpaceEnvelopeRing`. -/
theorem wholeSpaceDPAlgebra_completedRing (n : ℕ) :
    (wholeSpaceDPAlgebra hp).completedRing S.p n =
      ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u) := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The transition ring map of the cosimplicial degree is the structure map of
`...SmallSite.wholeSpaceEnvelopeRing`. -/
theorem wholeSpaceDPAlgebra_completedRingMap {m n : SimplexCategory} (φ : m ⟶ n)
    (x : (wholeSpaceDPAlgebra hp).completedRing S.p m.len) :
    (wholeSpaceDPAlgebra hp).completedRingMap S.p φ x =
      ((wholeSpaceEnvelopeRing hp).map φ).hom x := rfl

/-! ### The scalars of the levels, read through the two identifications -/

/-- **The reduction of a scalar of `D(n)` to the level `(n, e)` of the system of
[Stacks, Tag 07JN] agrees with the scalars of `...SmallSite.wholeSpaceLevelScalars`**, through the
identification `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` of the two realisations of `D(n)`.

The left-hand side is `...SmallSite.levelSectionsScalars`, built from
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`, and the right-hand side is the level component of
the identification `...SmallSite.envelopeLevelRingLimitEquiv` of the ring of the object `D(n)` the
system is built from with the limit of the section rings.  Both are the inverse of
`...SmallSite.wholeSpaceSystemLevelRingEquiv` applied to the class of the scalar; the only
difference is which of the two realisations the class is taken in, and
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` identifies them. -/
theorem levelSectionsScalars_eq_envelopeLevelRingLimitEquiv (n : SimplexCategory) (e : ℕ)
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u)) :
    levelSectionsScalars hp n e r =
      (envelopeLevelRingLimitEquiv hp n.len
        ((wholeSpaceSystemEnvelopeRingEquiv hp n.len).symm r)).val e := by
  rw [envelopeLevelRingLimitEquiv_apply_coe, levelSectionsScalars_apply]
  refine (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).injective ?_
  rw [RingEquiv.apply_symm_apply, wholeSpaceEnvelopeRingLevelEquiv_apply,
    RingEquiv.apply_symm_apply, Ideal.quotientEquiv_mk, RingEquiv.apply_symm_apply]

/-! ### The module `M(n)` of a cosimplicial degree -/

variable (Fc : QuasiCoherentCrystal S)

/-- **The module `M(n) = lim_e Γ((X, T(n)_e, δ(n)), ℱ)`** of the cosimplicial degree `n`, the
degree-`n` carrier of the cosimplicial module the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG] is built on.  It is
`...SmallSite.LevelScalars07JG.sections` at the system of levels of the degree `n`.

It is indexed by `SimplexCategory` and not by `ℕ` because the module structure below has to be
found by instance synthesis at a bare `SimplexCategory`
variable, which the discrimination tree does not reach from an index written `⦋n⦌`. -/
def wholeSpaceSections (n : SimplexCategory) : Type u :=
  (wholeSpaceLevelScalars hp n.len).sections Fc

/-- The additive group structure on `M(n)`. -/
instance (n : SimplexCategory) : AddCommGroup (wholeSpaceSections hp Fc n) :=
  inferInstanceAs (AddCommGroup ((wholeSpaceLevelScalars hp n.len).sections Fc))

/-- **`M(n)` is a module over the degree `n` of the completed cosimplicial envelope `D̂(*)`.**

`...SmallSite.LevelScalars07JG.sections` presents it as a module over the ring of the object
`D(n)` the system of [Stacks, Tag 07JN] is built from; the scalars are restricted along
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv`, which identifies that ring with the degree `n`
of `...SmallSite.wholeSpaceEnvelopeRing`. -/
instance wholeSpaceSectionsModule (n : SimplexCategory) :
    Module ((wholeSpaceEnvelopeRing hp).obj n) (wholeSpaceSections hp Fc n) :=
  Module.compHom ((wholeSpaceLevelScalars hp n.len).sections Fc)
    (wholeSpaceSystemEnvelopeRingEquiv hp n.len).symm.toRingHom

/-- The module structure `M(n)` carries over the ring of the object `D(n)` the system of
[Stacks, Tag 07JN] is built from, which is the one
`...SmallSite.LevelScalars07JG.sections` provides. -/
instance wholeSpaceSectionsEnvelopeModule (n : SimplexCategory) :
    Module ((wholeSpaceSystemEnvelope hp n.len).ring : Type u) (wholeSpaceSections hp Fc n) :=
  inferInstanceAs (Module ((wholeSpaceSystemEnvelope hp n.len).ring : Type u)
    ((wholeSpaceLevelScalars hp n.len).sections Fc))

/-- A scalar of `D(n)` and its image in `D̂(n)` act on `M(n)` in the same way. -/
theorem wholeSpaceSections_smul_envelopeRingEquiv (n : SimplexCategory)
    (a : ((wholeSpaceSystemEnvelope hp n.len).ring : Type u))
    (x : wholeSpaceSections hp Fc n) :
    (wholeSpaceSystemEnvelopeRingEquiv hp n.len a) • x = a • x := by
  change ((wholeSpaceSystemEnvelopeRingEquiv hp n.len).symm
    (wholeSpaceSystemEnvelopeRingEquiv hp n.len a)) • x = a • x
  rw [RingEquiv.symm_apply_apply]

/-- **`M(n)` is `p`-adically complete over `D̂(n)`.**

Over the ring of the object `D(n)` the system of [Stacks, Tag 07JN] is built from this is item
(07JB) of [Stacks, Lemma 60.17.3, Tag 07JG], proved as
`...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections`; the change of scalars along
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` is
`Crystalline.isAdicComplete_map_of_ringEquiv`, and the two `p`-adic ideals correspond by
`Crystalline.pAdicIdeal_map_ringHom`. -/
instance wholeSpaceSectionsIsAdicComplete (n : SimplexCategory) :
    IsAdicComplete (DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u)) S.p)
      (wholeSpaceSections hp Fc n) := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal
      (A := ((wholeSpaceSystemEnvelope hp n.len).ring : Type u)) S.p)
      (wholeSpaceSections hp Fc n) :=
    isPAdicallyComplete_wholeSpaceLevelScalars_sections hp n.len Fc
  have key := isAdicComplete_map_of_ringEquiv (wholeSpaceSystemEnvelopeRingEquiv hp n.len)
    (M := wholeSpaceSections hp Fc n)
    (wholeSpaceSections_smul_envelopeRingEquiv hp Fc n)
    (DividedPowers.pAdicIdeal (A := ((wholeSpaceSystemEnvelope hp n.len).ring : Type u)) S.p)
  rwa [_root_.Crystalline.pAdicIdeal_map_ringHom] at key

/-- **The component of an element of `M(n)` at the level `e`.** -/
def wholeSpaceSectionsVal {n : SimplexCategory} (m : wholeSpaceSections hp Fc n) (e : ℕ) :
    Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) :=
  ((wholeSpaceLevelScalars hp n.len).sectionsEquiv Fc m).val e

/-- **An element of `M(n)` from a compatible family of sections over the levels.** -/
def wholeSpaceSectionsMk {n : SimplexCategory}
    (f : ∀ e : ℕ, Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)))
    (hf : f ∈ levelSectionsLimit S ((wholeSpaceSystem S hp).obj (op n)) Fc) :
    wholeSpaceSections hp Fc n :=
  ⟨f, hf⟩

/-- The components of `wholeSpaceSectionsMk f hf` are the sections `f e`. -/
@[simp] theorem wholeSpaceSectionsVal_mk {n : SimplexCategory}
    (f : ∀ e : ℕ, Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)))
    (hf : f ∈ levelSectionsLimit S ((wholeSpaceSystem S hp).obj (op n)) Fc) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (wholeSpaceSectionsMk hp Fc f hf) e = f e := rfl

/-- An element of `M(n)` is determined by its components at the levels. -/
theorem wholeSpaceSectionsVal_injective {n : SimplexCategory}
    {m m' : wholeSpaceSections hp Fc n}
    (h : ∀ e, wholeSpaceSectionsVal hp Fc m e = wholeSpaceSectionsVal hp Fc m' e) : m = m' :=
  ((wholeSpaceLevelScalars hp n.len).sectionsEquiv Fc).injective (Subtype.ext (funext h))

/-- **The components of an element of `M(n)` form a compatible family.** -/
theorem wholeSpaceSectionsVal_restrict {n : SimplexCategory} (m : wholeSpaceSections hp Fc n)
    {e e' : ℕ} (h : e ⟶ e') :
    Fc.obj.val.map (((wholeSpaceSystem S hp).obj (op n)).map h).op
        (wholeSpaceSectionsVal hp Fc m e') =
      wholeSpaceSectionsVal hp Fc m e :=
  ((wholeSpaceLevelScalars hp n.len).sectionsEquiv Fc m).property h

/-- The component of a sum is the sum of the components. -/
@[simp] theorem wholeSpaceSectionsVal_add {n : SimplexCategory}
    (m m' : wholeSpaceSections hp Fc n) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (m + m') e =
      wholeSpaceSectionsVal hp Fc m e + wholeSpaceSectionsVal hp Fc m' e := rfl

/-- **A scalar of `D̂(n)` acts on `M(n)` level by level, through
`...SmallSite.levelSectionsScalars`.** -/
theorem wholeSpaceSectionsVal_smul {n : SimplexCategory}
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u))
    (m : wholeSpaceSections hp Fc n) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (r • m) e =
      levelSectionsScalars hp n e r • wholeSpaceSectionsVal hp Fc m e := by
  rw [levelSectionsScalars_eq_envelopeLevelRingLimitEquiv, ← wholeSpaceLevelScalars_ringEquiv]
  exact (wholeSpaceLevelScalars hp n.len).sectionsEquiv_smul Fc
    ((wholeSpaceSystemEnvelopeRingEquiv hp n.len).symm r) m e

/-! ### The cosimplicial transition map -/

section Transition

variable {m n : SimplexCategory} (φ : m ⟶ n)

/-- **The transition map `T(n)_e ⟶ T(m)_e`** of the system of [Stacks, Tag 07JN] in the
cosimplicial direction, at the level `e`.  Taking sections reverses it, which is what makes
`M(•)` cosimplicial. -/
abbrev wholeSpaceTrans (e : ℕ) :
    ((wholeSpaceSystem S hp).obj (op n)).obj e ⟶ ((wholeSpaceSystem S hp).obj (op m)).obj e :=
  ((wholeSpaceSystem S hp).map φ.op).app e

/-- The transition maps of the cosimplicial direction commute with those of the tower. -/
theorem wholeSpaceTrans_naturality {e e' : ℕ} (h : e ⟶ e') :
    ((wholeSpaceSystem S hp).obj (op n)).map h ≫ wholeSpaceTrans hp φ e' =
      wholeSpaceTrans hp φ e ≫ ((wholeSpaceSystem S hp).obj (op m)).map h :=
  ((wholeSpaceSystem S hp).map φ.op).naturality h

/-- **The levelwise restrictions of an element of `M(m)` along the cosimplicial transition form a
compatible family**, so they define an element of `M(n)`.  This is the naturality
`...SmallSite.wholeSpaceTrans_naturality` together with the compatibility of the components of the
element it starts from. -/
theorem wholeSpaceSectionsTransFun_mem (x : wholeSpaceSections hp Fc m) :
    (fun e ↦ Fc.obj.val.map (wholeSpaceTrans hp φ e).op (wholeSpaceSectionsVal hp Fc x e)) ∈
      levelSectionsLimit S ((wholeSpaceSystem S hp).obj (op n)) Fc := by
  intro e e' h
  rw [← PresheafOfModules.map_comp_apply]
  refine Eq.trans (PresheafOfModules.congr_map_apply Fc.obj.val
    (g := (((wholeSpaceSystem S hp).obj (op m)).map h).op ≫ (wholeSpaceTrans hp φ e).op)
    (by rw [← op_comp, ← op_comp, wholeSpaceTrans_naturality]) _) ?_
  rw [PresheafOfModules.map_comp_apply, wholeSpaceSectionsVal_restrict]

/-- **The cosimplicial transition map `M(m) → M(n)`** of the module `M(•)`: in each level `e` the
restriction map of `ℱ` along the transition `T(n)_e ⟶ T(m)_e` of the system.

It is **not** linear over `D̂(n)` — source and target are modules over different rings — but
semilinear over the structure map `D̂(m) → D̂(n)` of the completed cosimplicial envelope, which is
`...SmallSite.levelSectionsScalars_restriction` read on the limit by
`...SmallSite.wholeSpaceSectionsVal_smul`. -/
def wholeSpaceSectionsTransFun (x : wholeSpaceSections hp Fc m) : wholeSpaceSections hp Fc n :=
  wholeSpaceSectionsMk hp Fc
    (fun e ↦ Fc.obj.val.map (wholeSpaceTrans hp φ e).op (wholeSpaceSectionsVal hp Fc x e))
    (wholeSpaceSectionsTransFun_mem hp Fc φ x)

/-- The component at the level `e` of the transition of `x` is the restriction of the component
of `x` along `wholeSpaceTrans φ e`. -/
@[simp] theorem wholeSpaceSectionsVal_transFun (x : wholeSpaceSections hp Fc m) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (wholeSpaceSectionsTransFun hp Fc φ x) e =
      Fc.obj.val.map (wholeSpaceTrans hp φ e).op (wholeSpaceSectionsVal hp Fc x e) := rfl

/-- The cosimplicial transition map, as a semilinear map. -/
def wholeSpaceSectionsTrans :
    wholeSpaceSections hp Fc m →ₛₗ[((wholeSpaceEnvelopeRing hp).map φ).hom]
      wholeSpaceSections hp Fc n where
  toFun := wholeSpaceSectionsTransFun hp Fc φ
  map_add' x y := wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    simp only [wholeSpaceSectionsVal_transFun, wholeSpaceSectionsVal_add, map_add]
    rfl
  map_smul' r x := wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    rw [wholeSpaceSectionsVal_transFun, wholeSpaceSectionsVal_smul,
      PresheafOfModules.map_smul, levelSectionsScalars_restriction,
      wholeSpaceSectionsVal_smul, wholeSpaceSectionsVal_transFun]
    rfl

/-- The component at the level `e` of `wholeSpaceSectionsTrans φ x` is the restriction of the
component of `x` along `wholeSpaceTrans φ e`. -/
@[simp] theorem wholeSpaceSectionsVal_trans (x : wholeSpaceSections hp Fc m) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (wholeSpaceSectionsTrans hp Fc φ x) e =
      Fc.obj.val.map (wholeSpaceTrans hp φ e).op (wholeSpaceSectionsVal hp Fc x e) := rfl

end Transition

/-- The cosimplicial transition map of an identity is the identity. -/
theorem wholeSpaceSectionsTrans_id (n : SimplexCategory) (x : wholeSpaceSections hp Fc n) :
    wholeSpaceSectionsTrans hp Fc (𝟙 n) x = x :=
  wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    rw [wholeSpaceSectionsVal_trans]
    refine Eq.trans (PresheafOfModules.congr_map_apply Fc.obj.val
      (f := (((wholeSpaceSystem S hp).map (𝟙 n).op).app e).op)
      (g := 𝟙 (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) (by simp) _) ?_
    rw [Fc.obj.val.map_id, ModuleCat.restrictScalarsId'_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply]

/-- The cosimplicial transition maps compose. -/
theorem wholeSpaceSectionsTrans_comp {m n l : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ l)
    (x : wholeSpaceSections hp Fc m) :
    wholeSpaceSectionsTrans hp Fc (φ ≫ ψ) x =
      wholeSpaceSectionsTrans hp Fc ψ (wholeSpaceSectionsTrans hp Fc φ x) :=
  wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    rw [wholeSpaceSectionsVal_trans, wholeSpaceSectionsVal_trans, wholeSpaceSectionsVal_trans]
    refine Eq.trans (PresheafOfModules.congr_map_apply Fc.obj.val
      (f := (((wholeSpaceSystem S hp).map (φ ≫ ψ).op).app e).op)
      (g := (((wholeSpaceSystem S hp).map φ.op).app e).op ≫
        (((wholeSpaceSystem S hp).map ψ.op).app e).op) (by simp) _) ?_
    exact PresheafOfModules.map_comp_apply _ _ _ _

/-- **The cosimplicial module `M(•)` of a crystal in quasi-coherent `𝒪_{X/S}`-modules over the
completed cosimplicial envelope `D̂(*)`.**

This is the module half of the double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG], for a **general** quasi-coherent crystal: in cosimplicial
degree `b` the module `M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` of [Stacks, Proposition 60.20.1,
Tag 07JN], a module over `D̂(b)` by `...SmallSite.wholeSpaceSectionsModule`, with the restriction
maps of `ℱ` along the transition maps of the system as its semilinear cosimplicial transitions.

The carrier is the limit of sections and **not** a base change `D̂(b) ⊗̂_{D̂} M`: the two differ,
and only the first makes the identification of the column `a = 0` of `K` with the complex
`M(0) → M(1) → M(2) → ⋯` of [Stacks, Tag 07JN] true. -/
def wholeSpaceCosimplicialModule :
    CosimplicialCompletedModule.{u, u, u} (wholeSpaceDPAlgebra hp) S.p where
  carrier b := wholeSpaceSections hp Fc ⦋b⦌
  addCommGroup _b := inferInstance
  module b := inferInstanceAs
    (Module ((wholeSpaceEnvelopeRing hp).obj ⦋b⦌) (wholeSpaceSections hp Fc ⦋b⦌))
  map φ := wholeSpaceSectionsTrans hp Fc φ
  map_id_apply n x := wholeSpaceSectionsTrans_id hp Fc n x
  map_comp_apply φ ψ x := wholeSpaceSectionsTrans_comp hp Fc φ ψ x

/-- The carriers of `M(•)` are `p`-adically complete. -/
instance wholeSpaceCosimplicialModuleIsAdicComplete (b : ℕ) :
    IsAdicComplete (DividedPowers.pAdicIdeal
        (A := (wholeSpaceDPAlgebra hp).completedRing S.p b) S.p)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b) :=
  wholeSpaceSectionsIsAdicComplete hp Fc ⦋b⦌

/-- The carrier of `M(•)` in degree `b` is `wholeSpaceSections ⦋b⦌`. -/
@[simp] theorem wholeSpaceCosimplicialModule_carrier (b : ℕ) :
    (wholeSpaceCosimplicialModule hp Fc).carrier b = wholeSpaceSections hp Fc ⦋b⦌ := rfl

/-- The transition maps of `M(•)` are `wholeSpaceSectionsTrans`. -/
@[simp] theorem wholeSpaceCosimplicialModule_map {m n : SimplexCategory} (φ : m ⟶ n)
    (x : wholeSpaceSections hp Fc m) :
    (wholeSpaceCosimplicialModule hp Fc).map φ x = wholeSpaceSectionsTrans hp Fc φ x := rfl

/-- **The column `a = 0` of the double complex of a general quasi-coherent crystal is the
cosimplicial module `M(•)`.**

This is `Crystalline.CosimplicialCompletedModule.columnZeroIso` at the cosimplicial module built
in this file; its hypothesis, the `p`-adic completeness of each `M(b)`, is the instance
`...SmallSite.wholeSpaceCosimplicialModuleIsAdicComplete`. -/
def wholeSpaceColumnZeroIso :
    (wholeSpaceCosimplicialModule hp Fc).column 0 ≅
      (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial :=
  (wholeSpaceCosimplicialModule hp Fc).columnZeroIso

/-- **The cohomology of the Moore complex of the column `a = 0` is the cohomology of the Moore
complex of `M(•)`**, for a general quasi-coherent crystal. -/
def wholeSpaceMooreHomologyColumnZeroIso (j : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
        ((wholeSpaceCosimplicialModule hp Fc).column 0)).homology j ≅
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
        (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial).homology j :=
  (wholeSpaceCosimplicialModule hp Fc).mooreHomologyColumnZeroIso j

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
