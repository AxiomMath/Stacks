module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem

/-!
# Cokernels of coherent adic systems on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site.  This file shows that the category `Coh(F, 𝓘)` of coherent adic systems
of `AlgebraicGeometry.Space.CoherentAdicSystems` has cokernels, and that they are computed one
level at a time: the inclusion of `Coh(F, 𝓘)` into the inverse systems of `𝒪_F`-modules *creates*
the cokernel of a morphism, so the cokernel formed in `Coh(F, 𝓘)` may be analysed level by level.

The three defining conditions of a coherent adic system are checked separately for the levelwise
cokernel `(C_n)` of a morphism `f : (E_n) ⟶ (E'_n)`.

* Coherence: `C_n` is the cokernel of `E_n ⟶ E'_n`, colimits in a functor category being
  levelwise, and coherent modules on an algebraic space are closed under cokernels
  (`AlgebraicGeometry.Space.isCoherent_cokernel`).
* Annihilation by `𝓘 ^ (n + 1)`: the projection `E'_n ⟶ C_n` is surjective, and annihilation by
  a power of `𝓘` passes to a quotient.
* The transition `C_{n + 1} ⟶ C_n` is the quotient by `𝓘 ^ (n + 1) C_{n + 1}`: it kills that
  subsheaf, and a morphism out of `C_{n + 1}` killing it descends, first along
  `E'_{n + 1} ⟶ E'_{n + 1} / 𝓘 ^ (n + 1) E'_{n + 1} ≅ E'_n` and then along `E'_n ⟶ C_n`, the
  second step because the composite `E_n ⟶ E'_n ⟶ T` vanishes after the surjection
  `E_{n + 1} ⟶ E_n`.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicCokernel` — the levelwise cokernel, as an object of
  `Coh(F, 𝓘)`, with `AlgebraicGeometry.Space.coherentAdicCokernelπ` the projection onto it.
* `AlgebraicGeometry.Space.cokernelObjIso` — the identification of the value at a level of the
  cokernel of a morphism of inverse systems with the cokernel of its component there.

## Main results

* `AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_comp_eq_zero` and
  `AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_eq_zero_of_epi` — the two directions of the
  comparison of `𝓘 ^ k M` with `𝓘 ^ k` of a quotient of `M`.  The second is the only step of the
  file that uses the sheaf condition, in the form of local surjectivity of an epimorphism.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_cokernel` — **the levelwise cokernel of a
  morphism of coherent adic systems is a coherent adic system.**
* `AlgebraicGeometry.Space.coherentAdicCokernel_isCokernel` — the universal property of the
  cokernel in `Coh(F, 𝓘)`, in the elementary `∃!` form.
* `AlgebraicGeometry.Space.hasCokernels_coherentAdicSystems` — `Coh(F, 𝓘)` has all cokernels.
* `AlgebraicGeometry.Space.preservesColimitParallelPairι` — **the cokernel in `Coh(F, 𝓘)` is the
  levelwise one.**

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed, as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem`: the term at `n` is the Stacks source's
`E_{n + 1}`, which is why the annihilating exponent at level `n` is `n + 1`.

Both halves of the comparison of `𝓘 ^ k` with quotients are needed, and neither is formal.  The
inclusion `𝓘 ^ k M ⊆ (𝓘 ^ k Q)` pulled back along `M ⟶ Q` is the minimality of `𝓘 ^ k M` among
sheaf submodules containing `𝓘(U) ^ k M(U)` chartwise.  The reverse inclusion is not chartwise:
a section of `Q` over a chart need not lift to `M` there, only after passing to a covering.  It
is obtained by lifting locally, computing on the covering, and using that the target is a sheaf,
hence separated.  No surjectivity of an epimorphism on the sections over an affine chart is used
anywhere, and in particular the file is independent of Stacks 03DW.

The scheme-level argument for the same statement instead lifts sections over an affine open
outright; see `Stacks.Coherent.isCoherentAdicSystem_cokernel`.

The kernel in `Coh(F, 𝓘)` is *not* the levelwise one, so nothing here bears on the existence of
kernels; that is
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems`, and with it the abelian structure of
Stacks 089P (1) is `AlgebraicGeometry.Space.abelian_coherentAdicSystems`.  The levelwise
cokernel is what makes the normality of epimorphisms there a levelwise statement.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Ideal-power multiples and quotients -/

/-- A morphism which annihilates `𝓘 ^ k N` annihilates `𝓘 ^ k M` after precomposition with any
morphism `M ⟶ N`.

This is the minimality of `𝓘 ^ k M`: over a chart the image of `r • x` is `r` times the image of
`x`, so the preimage of `𝓘 ^ k N` is a sheaf submodule of `M` containing `𝓘(U) ^ k M(U)` over
every chart `U`. -/
theorem idealPowerMultiple_ι_comp_comp_eq_zero (k : ℕ) {M N T : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) (ψ : N ⟶ T) (h : (idealPowerMultiple B S hS F hF 𝓘 k N).ι ≫ ψ = 0) :
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ (φ ≫ ψ) = 0 := by
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k (φ ≫ ψ)).mpr fun U r hr x => ?_
  have hψ := (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k ψ).mp h U r hr
    (φ.val.app (op U) x)
  show ψ.val.app (op U) (φ.val.app (op U) (r • x)) = 0
  rw [(φ.val.app (op U)).hom.map_smul r x]
  exact hψ

/-- If `π : M ⟶ Q` is surjective and `ψ : Q ⟶ T` annihilates the image of `𝓘 ^ k M`, then `ψ`
annihilates `𝓘 ^ k Q`.

A section of `Q` over a chart need not be the image of a section of `M` over that chart, so the
argument is local: an epimorphism of sheaves of modules is locally surjective, a section of `𝓘`
restricts to a section of `𝓘` on a smaller chart, and the target is a sheaf, hence separated. -/
theorem idealPowerMultiple_ι_comp_eq_zero_of_epi (k : ℕ) {M Q T : Modules.{u, u} B S hS F hF}
    (π : M ⟶ Q) [Epi π] (ψ : Q ⟶ T)
    (h : (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ (π ≫ ψ) = 0) :
    (idealPowerMultiple B S hS F hF 𝓘 k Q).ι ≫ ψ = 0 := by
  have h' := (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k (π ≫ ψ)).mp h
  have key : ∀ (W : SmallEtale B S hS F) (ρ : chartRing B S hS F hF W),
      ρ ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 W ^ k → ∀ s : ToType (M.val.obj (op W)),
      ψ.val.app (op W) (π.val.app (op W) (ρ • s)) = 0 := by
    intro W ρ hρ s
    have hz := h' W ρ hρ s
    change ψ.val.app (op W) (π.val.app (op W) (ρ • s)) = 0 at hz
    exact hz
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k ψ).mpr fun U r hr x => ?_
  obtain ⟨Sv, hSv, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi π x
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hSv fun {V} g hg => ?_
  obtain ⟨t, ht'⟩ : ∃ t : ToType (M.val.obj (op V)),
      π.val.app (op V) t = Q.val.map g.op x := hlift g hg
  have e1 : Q.val.restrictₛₗ g.op (r • x)
      = chartRestrict (hF := hF) g r • Q.val.restrictₛₗ g.op x :=
    map_smulₛₗ (Q.val.restrictₛₗ g.op) r x
  have e2 : Q.val.restrictₛₗ g.op x = π.val.app (op V) t := ht'.symm
  refine (PresheafOfModules.naturality_apply ψ.val g.op (r • x)).symm.trans ?_
  show ψ.val.app (op V) (Q.val.restrictₛₗ g.op (r • x)) = 0
  have e3 : chartRestrict (hF := hF) g r • π.val.app (op V) t
      = π.val.app (op V) (chartRestrict (hF := hF) g r • t) :=
    ((π.val.app (op V)).hom.map_smul _ t).symm
  rw [e1, e2, e3]
  exact key V (chartRestrict (hF := hF) g r)
    (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 g k hr) t

/-- The transition map of a coherent adic system annihilates the subsheaf it divides by. -/
theorem idealPowerMultiple_ι_comp_map_succ_eq_zero {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (n : ℕ) :
    (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1)))).ι ≫
      E.map (homOfLE (Nat.le_succ n)).op = 0 := by
  obtain ⟨e, he⟩ := hE.2.2 n
  rw [← he, ← Category.assoc, cokernel.condition, zero_comp]

/-! ### Levelwise cokernels of inverse systems -/

/-- The value at a level of the cokernel of a morphism of inverse systems is the cokernel of its
component there: colimits in a functor category are computed levelwise. -/
def cokernelObjIso {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (cokernel g).obj n ≅ cokernel (g.app n) :=
  PreservesCokernel.iso ((evaluation ℕᵒᵖ (Modules.{u, u} B S hS F hF)).obj n) g

/-- Under `AlgebraicGeometry.Space.cokernelObjIso`, the component of the projection onto the
cokernel is the projection onto the cokernel of the component. -/
theorem app_comp_cokernelObjIso_hom {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y)
    (n : ℕᵒᵖ) :
    (cokernel.π g).app n ≫ (cokernelObjIso B S hS F hF g n).hom = cokernel.π (g.app n) :=
  PreservesCokernel.π_iso_hom ((evaluation ℕᵒᵖ (Modules.{u, u} B S hS F hF)).obj n) g

/-- Every component of the projection onto a levelwise cokernel is an epimorphism. -/
instance epi_cokernel_π_app {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    Epi ((cokernel.π g).app n) := by
  have h : cokernel.π (g.app n) ≫ (cokernelObjIso B S hS F hF g n).inv = (cokernel.π g).app n := by
    rw [← app_comp_cokernelObjIso_hom B S hS F hF g n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [← h]
  infer_instance

/-! ### The cokernel in `Coh(F, 𝓘)` -/

section Cokernel

variable {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E')

/-- The composite of a component of a morphism of coherent adic systems with the projection onto
the levelwise cokernel vanishes. -/
theorem app_comp_cokernel_π_app (n : ℕᵒᵖ) :
    f.hom.app n ≫ (cokernel.π f.hom).app n = 0 := by
  rw [← NatTrans.comp_app, cokernel.condition]
  simp

/-- The projection onto the levelwise cokernel is natural in the level. -/
theorem cokernel_π_app_comp_map_succ (n : ℕ) :
    (cokernel.π f.hom).app (op (n + 1)) ≫ (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op =
      E'.obj.map (homOfLE (Nat.le_succ n)).op ≫ (cokernel.π f.hom).app (op n) :=
  ((cokernel.π f.hom).naturality (homOfLE (Nat.le_succ n)).op).symm

/-- Each transition map of the levelwise cokernel is surjective. -/
instance epi_cokernel_map_succ (n : ℕ) :
    Epi ((cokernel f.hom).map (homOfLE (Nat.le_succ n)).op) := by
  have hepi : Epi (E'.obj.map (homOfLE (Nat.le_succ n)).op) :=
    epi_map_le_succ B S hS F hF 𝓘 E'.property n
  have hcc : Epi ((cokernel.π f.hom).app (op (n + 1)) ≫
      (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op) := by
    rw [cokernel_π_app_comp_map_succ B S hS F hF 𝓘 f n]
    infer_instance
  exact epi_of_epi ((cokernel.π f.hom).app (op (n + 1))) _

/-- Every term of the levelwise cokernel of a morphism of coherent adic systems is coherent. -/
theorem isCoherent_cokernel_obj (n : ℕ) :
    IsCoherent B S hS F hF ((cokernel f.hom).obj (op n)) :=
  (isCoherent.{u, u} B S hS F hF).prop_of_iso (cokernelObjIso B S hS F hF f.hom (op n)).symm
    (isCoherent_cokernel B S hS F hF (E.property.1 n) (E'.property.1 n) (f.hom.app (op n)))

/-- The term at level `n` of the levelwise cokernel is annihilated by `𝓘 ^ (n + 1)`, being a
quotient of the term at that level of the target. -/
theorem idealPowerMultiple_cokernel_obj_eq_bot (n : ℕ) :
    idealPowerMultiple B S hS F hF 𝓘 (n + 1) ((cokernel f.hom).obj (op n)) = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mpr
    (isPowAnnihilated_of_epi B S hS F hF 𝓘 (n + 1) ((cokernel.π f.hom).app (op n))
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mp (E'.property.2.1 n)))

/-- Each transition map of the levelwise cokernel annihilates `𝓘 ^ (n + 1)` of its source. -/
theorem idealPowerMultiple_ι_comp_cokernel_map_eq_zero (n : ℕ) :
    (idealPowerMultiple B S hS F hF 𝓘 (n + 1) ((cokernel f.hom).obj (op (n + 1)))).ι ≫
      (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op = 0 := by
  refine idealPowerMultiple_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 (n + 1)
    ((cokernel.π f.hom).app (op (n + 1))) _ ?_
  rw [cokernel_π_app_comp_map_succ B S hS F hF 𝓘 f n, ← Category.assoc,
    idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E'.property n, zero_comp]

/-- A morphism out of the term at level `n + 1` of the levelwise cokernel which annihilates
`𝓘 ^ (n + 1)` of that term factors through the transition map.

The morphism is pulled back to `E'_{n + 1}`, where it still annihilates `𝓘 ^ (n + 1)`, hence
descends to `E'_n`; the descent kills the component of `f` at level `n`, because it does so after
the surjection `E_{n + 1} ⟶ E_n`, and therefore descends again to the cokernel of that
component. -/
theorem exists_desc_of_cokernel_map_succ (n : ℕ) {T : Modules.{u, u} B S hS F hF}
    (h : (cokernel f.hom).obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      ((cokernel f.hom).obj (op (n + 1)))).ι ≫ h = 0) :
    ∃ d : (cokernel f.hom).obj (op n) ⟶ T,
      (cokernel f.hom).map (homOfLE (Nat.le_succ n)).op ≫ d = h := by
  have hι := idealPowerMultiple_ι_comp_comp_eq_zero B S hS F hF 𝓘 (n + 1)
    ((cokernel.π f.hom).app (op (n + 1))) h hh
  obtain ⟨d, hd⟩ := exists_desc_of_transition B S hS F hF 𝓘 E'.property n _ hι
  have hfd : f.hom.app (op n) ≫ d = 0 := by
    have hepi : Epi (E.obj.map (homOfLE (Nat.le_succ n)).op) :=
      epi_map_le_succ B S hS F hF 𝓘 E.property n
    refine (cancel_epi (E.obj.map (homOfLE (Nat.le_succ n)).op)).mp ?_
    rw [comp_zero, ← Category.assoc, f.hom.naturality, Category.assoc, hd, ← Category.assoc,
      app_comp_cokernel_π_app B S hS F hF 𝓘 f (op (n + 1)), zero_comp]
  refine ⟨(cokernelObjIso B S hS F hF f.hom (op n)).hom ≫
    cokernel.desc (f.hom.app (op n)) d hfd, ?_⟩
  refine (cancel_epi ((cokernel.π f.hom).app (op (n + 1)))).mp ?_
  rw [← Category.assoc, cokernel_π_app_comp_map_succ B S hS F hF 𝓘 f n, Category.assoc,
    ← Category.assoc ((cokernel.π f.hom).app (op n)),
    app_comp_cokernelObjIso_hom B S hS F hF f.hom (op n), cokernel.π_desc, hd]

/-- Each transition map of the levelwise cokernel exhibits its target as the quotient of its
source by `𝓘 ^ (n + 1)`. -/
def cokernelMapSuccIsColimit (n : ℕ) :
    IsColimit (CokernelCofork.ofπ ((cokernel f.hom).map (homOfLE (Nat.le_succ n)).op)
      (idealPowerMultiple_ι_comp_cokernel_map_eq_zero B S hS F hF 𝓘 f n)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk =>
    ⟨(exists_desc_of_cokernel_map_succ B S hS F hF 𝓘 f n k hk).choose,
      (exists_desc_of_cokernel_map_succ B S hS F hF 𝓘 f n k hk).choose_spec⟩

/-- **The levelwise cokernel of a morphism of coherent adic systems is a coherent adic
system.** -/
theorem isCoherentAdicSystem_cokernel :
    IsCoherentAdicSystem B S hS F hF 𝓘 (cokernel f.hom) :=
  ⟨isCoherent_cokernel_obj B S hS F hF 𝓘 f,
    idealPowerMultiple_cokernel_obj_eq_bot B S hS F hF 𝓘 f, fun n =>
    ⟨_, IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        ((cokernel f.hom).obj (op (n + 1)))).ι)
      (cokernelMapSuccIsColimit B S hS F hF 𝓘 f n) WalkingParallelPair.one⟩⟩

/-- The cokernel of a morphism of coherent adic systems, formed one level at a time. -/
def coherentAdicCokernel : CoherentAdicSystems B S hS F hF 𝓘 :=
  ⟨cokernel f.hom, isCoherentAdicSystem_cokernel B S hS F hF 𝓘 f⟩

/-- The projection onto the cokernel of a morphism of coherent adic systems. -/
def coherentAdicCokernelπ : E' ⟶ coherentAdicCokernel B S hS F hF 𝓘 f :=
  ObjectProperty.homMk (cokernel.π f.hom)

/-- A morphism of coherent adic systems composed with the projection onto its cokernel
vanishes. -/
theorem comp_coherentAdicCokernelπ : f ≫ coherentAdicCokernelπ B S hS F hF 𝓘 f = 0 :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (cokernel.condition f.hom)

/-- **The universal property of the cokernel of a morphism of coherent adic systems.** -/
theorem coherentAdicCokernel_isCokernel :
    ∀ (K : CoherentAdicSystems B S hS F hF 𝓘) (g : E' ⟶ K), f.hom ≫ g.hom = 0 →
      ∃! k : coherentAdicCokernel B S hS F hF 𝓘 f ⟶ K,
        (coherentAdicCokernelπ B S hS F hF 𝓘 f).hom ≫ k.hom = g.hom := by
  intro K g hg
  refine ⟨ObjectProperty.homMk (cokernel.desc f.hom g.hom hg), cokernel.π_desc _ _ _, ?_⟩
  intro k hk
  exact ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘)
    ((cancel_epi (cokernel.π f.hom)).1 (hk.trans (cokernel.π_desc _ _ _).symm))

/-- The inclusion of the coherent adic systems into all inverse systems creates the cokernel of a
morphism of coherent adic systems, the levelwise cokernel being one. -/
instance createsColimitParallelPairι :
    CreatesColimit (parallelPair f 0)
      (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) :=
  createsColimitFullSubcategoryInclusion' (parallelPair f 0)
    ((isColimitMapCoconeCoforkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 f)).symm (cokernelIsCokernel f.hom))
    (isCoherentAdicSystem_cokernel B S hS F hF 𝓘 f)

/-- The cokernel of a morphism of coherent adic systems exists. -/
instance hasCokernel_coherentAdicSystems : HasCokernel f :=
  hasColimit_of_created (parallelPair f 0)
    (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))

/-- **The cokernel in `Coh(F, 𝓘)` is the levelwise cokernel.** -/
instance preservesColimitParallelPairι :
    PreservesColimit (parallelPair f 0)
      (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) :=
  preservesColimit_of_createsColimit_and_hasColimit _ _

/-- The cokernel cofork of `AlgebraicGeometry.Space.coherentAdicCokernelπ` is a colimit:
`AlgebraicGeometry.Space.coherentAdicCokernel` is the cokernel of `f` in `Coh(F, 𝓘)`. -/
def coherentAdicCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (coherentAdicCokernelπ B S hS F hF 𝓘 f)
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 f)) :=
  isColimitOfReflects (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
    ((isColimitMapCoconeCoforkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 f)).symm (cokernelIsCokernel f.hom))

end Cokernel

/-- **The category `Coh(F, 𝓘)` of coherent adic systems on an algebraic space has all
cokernels.** -/
instance hasCokernels_coherentAdicSystems :
    HasCokernels (CoherentAdicSystems B S hS F hF 𝓘) where
  has_colimit f := hasCokernel_coherentAdicSystems B S hS F hF 𝓘 f

end AlgebraicGeometry.Space

end
