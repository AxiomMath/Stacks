module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.Acyclicity
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.OrderedCechComparison
public import StacksFrontier.RingTheory.LocalCohomology.CechModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections of the extended alternating Čech complex over an affine open

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions and let `ℱ` be a
quasi-coherent `𝒪_X`-module.  Over an *affine* open `V ⊆ X` the complex of sections of the
extended alternating Čech complex of Stacks 0G7I is the algebraic extended alternating Čech
complex `C^•(f₁|_V, …, f_c|_V; Γ(ℱ, V))`, `Cech.cechComplex`.

The reason is Stacks 01P7: the intersection of `V` with the principal opens of a set `T` of the
equations is the principal open of `∏_{i ∈ T} f_i|_V` inside `V`, and on a quasi-compact
quasi-separated open the sections of a quasi-coherent module over a principal open are the
localization of its sections away from the defining function.  An affine open is quasi-compact
and quasi-separated, so

`Γ(ℱ, V ∩ ⋂_{i ∈ T} X_{f_i}) = Γ(ℱ, V)_{∏_{i ∈ T} f_i|_V}`,

which is the Čech localization `Cech.cechMod` attached to `T`. These identifications, over all
strictly increasing tuples, match the ordered Čech differential of Stacks 01FJ with `Cech.cechD`.

The vanishing of Stacks 0G7P in degrees below the number of equations combines this comparison
with `Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat`.

## Main definitions

* `Stacks.Perfect.AffineCechSections.eqn` — the equations restricted to `V`.
* `Stacks.Perfect.AffineCechSections.cechOpen` — the open attached to a finite set of indices.
* `Stacks.Perfect.AffineCechSections.sectionsEquiv` — **the sections of `ℱ` over a Čech open of
  an affine open are the Čech localization of its sections over that affine open.**
* `Stacks.Perfect.AffineCechSections.sectionsEquivOfEq` — the same comparison at an open merely
  *equal* to a Čech open, which is the shape the Čech cochains present it in.
* `Stacks.Perfect.AffineCechSections.ordCochainEquivCechTerm` — the degreewise comparison of the
  ordered Čech cochains over `V` with the terms of `Cech.cechComplex`.
* `Stacks.Perfect.AffineCechSections.complexIso` — **the complex of sections over `V` is the
  algebraic extended alternating Čech complex of the restricted equations.**

## Main results

* `Stacks.Perfect.AffineCechSections.cechOpen_eq` and
  `Stacks.Perfect.AffineCechSections.inter_eq_cechOpen` — the intersection attached to a tuple is
  the principal open of the product of the corresponding equations.
* `Stacks.Perfect.AffineCechSections.sectionsEquiv_restrict` and
  `Stacks.Perfect.AffineCechSections.sectionsEquivOfEq_restrict` — **naturality in the set of
  indices**: restriction becomes the transition map `Cech.cechι` of the localizations.

## Implementation notes

The comparison is stated for an open `W` together with a proof that `W` *equals* the Čech open
attached to a set of indices: the opens indexing the ordered Čech cochains of
`ExtendedAlternatingCechData` are the intersections `⋂_k (V ⊓ X_{f_{σ k}})`, which are equal to,
but not syntactically, the principal open of a product.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0G6H](https://stacks.math.columbia.edu/tag/0G6H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AffineCechSections

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (V : X.Opens)

/-! ### The equations restricted to an open, and the opens they cut out -/

/-- The global equations restricted to `V`. -/
public def eqn (i : Fin c) : Γ(X, V) := X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (f i)

/-- The principal open of a restricted equation is the part of the original principal open
lying in `V`. -/
public theorem basicOpen_eqn (i : Fin c) : X.basicOpen (eqn f V i) = V ⊓ X.basicOpen (f i) :=
  X.basicOpen_res _ _

/-- The open attached to a finite set `T` of indices: the principal open, inside `V`, of the
product of the corresponding restricted equations. -/
public def cechOpen (T : Finset (Fin c)) : X.Opens := X.basicOpen (∏ i ∈ T, eqn f V i)

/-- The open attached to `T` is contained in `V`. -/
public theorem cechOpen_le (T : Finset (Fin c)) : cechOpen f V T ≤ V := X.basicOpen_le _

/-- The open attached to `T` is the part of the intersection of the principal opens of the
equations indexed by `T` that lies in `V`. -/
public theorem cechOpen_eq (T : Finset (Fin c)) :
    cechOpen f V T = V ⊓ ⨅ i ∈ T, X.basicOpen (f i) := by
  classical
  unfold cechOpen
  induction T using Finset.induction with
  | empty => simp [Scheme.basicOpen_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert,
        basicOpen_eqn, inf_assoc, inf_left_comm (X.basicOpen (f a)) V, ← inf_assoc, inf_idem]

/-- Enlarging the set of indices shrinks the open attached to it. -/
public theorem cechOpen_mono {T T' : Finset (Fin c)} (h : T ⊆ T') :
    cechOpen f V T' ≤ cechOpen f V T := by
  rw [cechOpen_eq, cechOpen_eq]
  exact inf_le_inf_left _ (iInf_le_iInf_of_subset h)

/-- **The intersection attached to a tuple is the open attached to the set of its entries.** -/
public theorem inter_eq_cechOpen {p : ℕ} (σ : Fin (p + 1) → Fin c) :
    CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) σ
      = cechOpen f V (Finset.image σ Finset.univ) := by
  classical
  rw [cechOpen_eq]
  refine le_antisymm ?_ ?_
  · refine le_inf ((iInf_le _ (0 : Fin (p + 1))).trans inf_le_left) (le_iInf₂ fun i hi => ?_)
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi
    exact (iInf_le _ k).trans inf_le_right
  · exact le_iInf fun k => le_inf inf_le_left
      (inf_le_right.trans (iInf₂_le _ (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)))

/-! ### The sections over a Čech open are a Čech localization -/

variable (F : X.Modules) [F.IsQuasicoherent] (hV : IsAffineOpen V)

/-- The `Γ(X, V)`-module structure on the sections of `F` over the Čech open attached to `T`. -/
public abbrev modCechOpen (T : Finset (Fin c)) : Module Γ(X, V) Γ(F, cechOpen f V T) :=
  Module.compHom Γ(F, cechOpen f V T)
    (X.presheaf.map (homOfLE (cechOpen_le f V T)).op).hom

/-- Restriction of sections from `V` to the Čech open attached to `T`. -/
public abbrev resCech (T : Finset (Fin c)) :
    letI := modCechOpen f V F T
    Γ(F, V) →ₗ[Γ(X, V)] Γ(F, cechOpen f V T) :=
  letI := modCechOpen f V F T
  Scheme.Modules.restrictionLinearMap F (homOfLE (cechOpen_le f V T))

include hV in
/-- **Stacks 01P7 at a Čech open.**  On an affine open, restriction of the sections of a
quasi-coherent module to the open attached to `T` is localization at `∏_{i ∈ T} f_i|_V`. -/
public theorem isLocalizedModule_resCech (T : Finset (Fin c)) :
    letI := modCechOpen f V F T
    IsLocalizedModule (Cech.cechSub (eqn f V) T) (resCech f V F T) :=
  isLocalizedModule_restriction_basicOpen_of_qcqs F hV.isCompact hV.isQuasiSeparated _

/-- **The sections of a quasi-coherent module over a Čech open of an affine open are the Čech
localization of its sections over that affine open.** -/
public def sectionsEquiv (T : Finset (Fin c)) :
    Γ(F, cechOpen f V T) ≃+ Cech.cechMod (eqn f V) Γ(F, V) T :=
  letI := modCechOpen f V F T
  letI := isLocalizedModule_resCech f V F hV T
  (IsLocalizedModule.linearEquiv (Cech.cechSub (eqn f V) T) (resCech f V F T)
    (LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T) Γ(F, V))).toAddEquiv

/-- The comparison carries the restriction of a section over `V` to the constant fraction. -/
@[simp] theorem sectionsEquiv_res (T : Finset (Fin c)) (m : Γ(F, V)) :
    sectionsEquiv f V F hV T (F.presheaf.map (homOfLE (cechOpen_le f V T)).op m)
      = LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T) Γ(F, V) m :=
  let := modCechOpen f V F T
  let := isLocalizedModule_resCech f V F hV T
  IsLocalizedModule.linearEquiv_apply (Cech.cechSub (eqn f V) T) (resCech f V F T) _ m

/-- Restriction between two Čech opens, as a `Γ(X, V)`-linear map. -/
public def resCechLE {T T' : Finset (Fin c)} (h : T ⊆ T') :
    letI := modCechOpen f V F T
    letI := modCechOpen f V F T'
    Γ(F, cechOpen f V T) →ₗ[Γ(X, V)] Γ(F, cechOpen f V T') :=
  letI := modCechOpen f V F T
  letI := modCechOpen f V F T'
  { toFun := F.presheaf.map (homOfLE (cechOpen_mono f V h)).op
    map_add' := map_add _
    map_smul' := fun a x => by
      have hX : X.presheaf.map (homOfLE (cechOpen_mono f V h)).op
            (X.presheaf.map (homOfLE (cechOpen_le f V T)).op a)
          = X.presheaf.map (homOfLE (cechOpen_le f V T')).op a := by
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
        exact congrArg (fun g => X.presheaf.map (Opposite.op g) a) (Subsingleton.elim _ _)
      exact (F.map_smul (homOfLE (cechOpen_mono f V h))
        (X.presheaf.map (homOfLE (cechOpen_le f V T)).op a) x).trans
          (congrArg (fun z => z • F.presheaf.map (homOfLE (cechOpen_mono f V h)).op x) hX) }

include hV in
/-- **Naturality in the set of indices**: restriction from the open attached to `T` to the open
attached to a larger `T'` becomes the transition map of the localizations. -/
public theorem sectionsEquiv_restrict {T T' : Finset (Fin c)} (h : T ⊆ T')
    (x : Γ(F, cechOpen f V T)) :
    sectionsEquiv f V F hV T' (F.presheaf.map (homOfLE (cechOpen_mono f V h)).op x)
      = Cech.cechι (eqn f V) Γ(F, V) h (sectionsEquiv f V F hV T x) := by
  let := modCechOpen f V F T
  let := modCechOpen f V F T'
  let := isLocalizedModule_resCech f V F hV T
  let := isLocalizedModule_resCech f V F hV T'
  have key : ((IsLocalizedModule.linearEquiv (Cech.cechSub (eqn f V) T') (resCech f V F T')
        (LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T') Γ(F, V))).toLinearMap ∘ₗ
          resCechLE f V F h)
      = (Cech.cechι (eqn f V) Γ(F, V) h) ∘ₗ
        (IsLocalizedModule.linearEquiv (Cech.cechSub (eqn f V) T) (resCech f V F T)
          (LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T) Γ(F, V))).toLinearMap := by
    refine IsLocalizedModule.ext (Cech.cechSub (eqn f V) T) (resCech f V F T)
      (Cech.isUnit_algebraMap (eqn f V) Γ(F, V) h
        (LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T') Γ(F, V))) ?_
    refine LinearMap.ext fun m => ?_
    have hL : (resCechLE f V F h) (resCech f V F T m) = resCech f V F T' m := by
      change F.presheaf.map _ (F.presheaf.map _ m) = F.presheaf.map _ m
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact congrArg (fun g => F.presheaf.map (Opposite.op g) m) (Subsingleton.elim _ _)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hL,
      IsLocalizedModule.linearEquiv_apply]
    exact (Cech.cechι_mk (eqn f V) Γ(F, V) h m).symm
  exact LinearMap.congr_fun key x

/-! ### The comparison at an open equal to a Čech open -/

/-- The comparison of `Stacks.Perfect.AffineCechSections.sectionsEquiv` at an open merely
*equal* to the Čech open attached to `T`. -/
public def sectionsEquivOfEq (T : Finset (Fin c)) {W : X.Opens} (hW : W = cechOpen f V T) :
    Γ(F, W) ≃+ Cech.cechMod (eqn f V) Γ(F, V) T := by
  subst hW; exact sectionsEquiv f V F hV T

/-- At the Čech open itself, `sectionsEquivOfEq` is `sectionsEquiv`. -/
@[simp] theorem sectionsEquivOfEq_cechOpen (T : Finset (Fin c)) :
    sectionsEquivOfEq f V F hV T (W := cechOpen f V T) rfl = sectionsEquiv f V F hV T := rfl

/-- The comparison at an open equal to a Čech open carries the restriction of a section over `V`
to the constant fraction. -/
public theorem sectionsEquivOfEq_res (T : Finset (Fin c)) {W : X.Opens} (hW : W = cechOpen f V T)
    (hWV : W ≤ V) (m : Γ(F, V)) :
    sectionsEquivOfEq f V F hV T hW (F.presheaf.map (homOfLE hWV).op m)
      = LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T) Γ(F, V) m := by
  subst hW
  exact sectionsEquiv_res f V F hV T m

/-- **Naturality in the set of indices**, at opens equal to the Čech opens. -/
public theorem sectionsEquivOfEq_restrict {T T' : Finset (Fin c)} (h : T ⊆ T')
    {W W' : X.Opens} (hW : W = cechOpen f V T) (hW' : W' = cechOpen f V T') (hWW' : W' ≤ W)
    (x : Γ(F, W)) :
    sectionsEquivOfEq f V F hV T' hW' (F.presheaf.map (homOfLE hWW').op x)
      = Cech.cechι (eqn f V) Γ(F, V) h (sectionsEquivOfEq f V F hV T hW x) := by
  subst hW; subst hW'
  exact sectionsEquiv_restrict f V F hV h x

/-! ### Strictly increasing tuples and sets of indices -/

/-- Strictly increasing tuples of indices in `Fin c` are the same as strictly increasing tuples
in its lift `ULift (Fin c)`. -/
public def upIndex (p : ℕ) : CechCochains.OrdIndex (I := Fin c) p ≃
    CechCochains.OrdIndex (I := ULift.{u} (Fin c)) p where
  toFun σ := ⟨fun k => ULift.up (σ.1 k), fun _ _ hab => by simpa using σ.2 hab⟩
  invFun σ := ⟨fun k => (σ.1 k).down, fun _ _ hab => by simpa using σ.2 hab⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The set of entries of a strictly increasing tuple**, as an index of the extended
alternating Čech complex. -/
public abbrev ordIdx (p : ℕ) (σ : CechCochains.OrdIndex (I := Fin c) p) :
    {t : Finset (Fin c) // t.card = p + 1} :=
  ⟨Finset.image σ.1 Finset.univ, by
    classical
    rw [Finset.card_image_of_injective _ σ.2.injective, Finset.card_univ, Fintype.card_fin]⟩

/-- A strictly increasing tuple is the increasing enumeration of the set of its entries. -/
public theorem orderEmbOfFin_ordIdx {p : ℕ} (σ : CechCochains.OrdIndex (I := Fin c) p) :
    (σ.1 : Fin (p + 1) → Fin c) = (ordIdx p σ).1.orderEmbOfFin (ordIdx p σ).2 :=
  Finset.orderEmbOfFin_unique (ordIdx p σ).2
    (fun k => Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩) σ.2

/-- **Strictly increasing tuples are determined by the set of their entries.** -/
public theorem ordIdx_injective (p : ℕ) :
    Function.Injective (ordIdx (c := c) p) := fun σ τ h => by
  refine Subtype.ext ((orderEmbOfFin_ordIdx σ).trans ?_)
  rw [h]
  exact (orderEmbOfFin_ordIdx τ).symm

/-- **Every set of indices of the right size is the set of entries of a tuple.** -/
public theorem exists_ordIdx_eq (p : ℕ) (T : {t : Finset (Fin c) // t.card = p + 1}) :
    ∃ σ, ordIdx p σ = T :=
  ⟨⟨T.1.orderEmbOfFin T.2, (T.1.orderEmbOfFin T.2).strictMono⟩, Subtype.ext (by
    refine Finset.coe_injective ?_
    change ((Finset.image (fun k => T.1.orderEmbOfFin T.2 k) Finset.univ : Finset (Fin c)) :
      Set (Fin c)) = (T.1 : Set (Fin c))
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin T.1 T.2)⟩

/-- The underlying set of `ordIdx p σ` is the image of `σ`. -/
public theorem ordIdx_val (p : ℕ) (σ : CechCochains.OrdIndex (I := Fin c) p) :
    (ordIdx p σ).1 = Finset.image σ.1 Finset.univ := rfl

/-- The intersection attached to a strictly increasing tuple is the Čech open attached to the
set of its entries. -/
public theorem inter_eq_cechOpen_ordIdx {p : ℕ} (σ : CechCochains.OrdIndex (I := Fin c) p) :
    CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) σ.1 = cechOpen f V (ordIdx p σ).1 :=
  inter_eq_cechOpen f V σ.1

/-- The entries of a face of a tuple are among the entries of the tuple. -/
public theorem ordIdx_omit_subset {p : ℕ} (σ : CechCochains.OrdIndex (I := Fin c) (p + 1))
    (j : Fin (p + 2)) :
    (ordIdx p ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩).1 ⊆
      (ordIdx (p + 1) σ).1 := by
  classical
  intro i hi
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi
  exact Finset.mem_image.2 ⟨j.succAbove k, Finset.mem_univ _, rfl⟩

/-! ### The degreewise comparison of the ordered Čech cochains with the Čech terms -/

/-- The comparison of a cochain over the affine open `V` with the Čech term, as a map: a cochain
is sent to the sum of its values, each placed in the summand indexed by the set of entries of
the corresponding strictly increasing tuple. -/
public def ordCochainToCechTerm (p : ℕ)
    (s : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p) :
    Cech.cechTerm (eqn f V) Γ(F, V) (p + 1) :=
  ∑ σ : CechCochains.OrdIndex (I := Fin c) p,
    DirectSum.lof Γ(X, V) {t : Finset (Fin c) // t.card = p + 1}
      (fun t => Cech.cechMod (eqn f V) Γ(F, V) t.1) (ordIdx p σ)
      (sectionsEquivOfEq f V F hV (ordIdx p σ).1 (inter_eq_cechOpen_ordIdx f V σ) (s σ))

/-- The component of the comparison at the set of entries of a tuple is the value of the cochain
at that tuple: all the other summands are indexed by different sets. -/
public theorem cechComponent_ordCochainToCechTerm (p : ℕ)
    (s : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p)
    (σ₀ : CechCochains.OrdIndex (I := Fin c) p) :
    Stacks.LocalCohomology.cechComponent (eqn f V) (ModuleCat.of Γ(X, V) Γ(F, V)) (p + 1)
        (ordIdx p σ₀) (ordCochainToCechTerm f V F hV p s) =
      sectionsEquivOfEq f V F hV (ordIdx p σ₀).1 (inter_eq_cechOpen_ordIdx f V σ₀) (s σ₀) :=
  (map_sum (Stacks.LocalCohomology.cechComponent (eqn f V)
      (ModuleCat.of Γ(X, V) Γ(F, V)) (p + 1) (ordIdx p σ₀)) _ Finset.univ).trans
    ((Finset.sum_eq_single_of_mem σ₀ (Finset.mem_univ _) (fun _ _ hτ =>
      Stacks.LocalCohomology.cechComponent_lof_of_ne _ _ _ _
        (fun h => hτ (ordIdx_injective p (Subtype.ext h))) _)).trans
      ((Stacks.LocalCohomology.cechComponent_lof_of_eq _ _ _ _ rfl _).trans
        (Stacks.LocalCohomology.cechι_le_refl_apply _ _ _)))

/-- **The degreewise comparison** `Č^p_ord(V) ≅ C^{p+1}(f|_V; Γ(ℱ, V))`. -/
public def ordCochainEquivCechTerm (p : ℕ) :
    CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf F) p
      ≃+ Cech.cechTerm (eqn f V) Γ(F, V) (p + 1) :=
  AddEquiv.mk'
    { toFun := ordCochainToCechTerm f V F hV p
      invFun := fun x σ => (sectionsEquivOfEq f V F hV (ordIdx p σ).1
        (inter_eq_cechOpen_ordIdx f V σ)).symm
          (Stacks.LocalCohomology.cechComponent (eqn f V) (ModuleCat.of Γ(X, V) Γ(F, V))
            (p + 1) (ordIdx p σ) x)
      left_inv := fun s => by
        funext σ
        exact (congrArg (sectionsEquivOfEq f V F hV (ordIdx p σ).1
              (inter_eq_cechOpen_ordIdx f V σ)).symm
            (cechComponent_ordCochainToCechTerm f V F hV p s σ)).trans
          ((sectionsEquivOfEq f V F hV (ordIdx p σ).1
            (inter_eq_cechOpen_ordIdx f V σ)).symm_apply_apply (s σ))
      right_inv := fun x => by
        refine DirectSum.ext fun t => ?_
        obtain ⟨σ, rfl⟩ := exists_ordIdx_eq p t
        exact (cechComponent_ordCochainToCechTerm f V F hV p _ σ).trans
          ((sectionsEquivOfEq f V F hV (ordIdx p σ).1
            (inter_eq_cechOpen_ordIdx f V σ)).apply_symm_apply _) }
    (fun s t => by
      refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) Finset.sum_add_distrib
      exact (congrArg (DirectSum.lof Γ(X, V) {t : Finset (Fin c) // t.card = p + 1}
          (fun t => Cech.cechMod (eqn f V) Γ(F, V) t.1) (ordIdx p σ))
        (map_add (sectionsEquivOfEq f V F hV (ordIdx p σ).1
          (inter_eq_cechOpen_ordIdx f V σ)) (s σ) (t σ))).trans
        (map_add _ _ _))

/-! ### The comparison is compatible with the differentials -/

omit [F.IsQuasicoherent] in
/-- The restriction maps of the abelian presheaf underlying a module are the restriction maps
of the module. -/
public theorem restr_modulePresheaf {W W' : X.Opens} (h : W' ≤ W) (x : Γ(F, W)) :
    CechCochains.restr (Scheme.Modules.presheaf F) h x = F.presheaf.map (homOfLE h).op x := rfl

/-- The ordered Čech differential over `V`, under the comparison of the sections with the Čech
localizations, is the alternating sum of the transition maps. -/
public theorem sectionsEquivOfEq_ordD (p : ℕ)
    (s : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p)
    (σ : CechCochains.OrdIndex (I := Fin c) (p + 1)) :
    sectionsEquivOfEq f V F hV (ordIdx (p + 1) σ).1 (inter_eq_cechOpen_ordIdx f V σ)
        (CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i))
          (Scheme.Modules.presheaf F) p s σ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι (eqn f V) Γ(F, V) (ordIdx_omit_subset σ j)
          (sectionsEquivOfEq f V F hV
            (ordIdx p ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩).1
            (inter_eq_cechOpen_ordIdx f V _)
            (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩)) := by
  have hd : CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i))
        (Scheme.Modules.presheaf F) p s σ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (Scheme.Modules.presheaf F)
          (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) σ.1 j)
          (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩) := rfl
  refine (congrArg (sectionsEquivOfEq f V F hV (ordIdx (p + 1) σ).1
    (inter_eq_cechOpen_ordIdx f V σ)) hd).trans ?_
  refine (map_sum (sectionsEquivOfEq f V F hV (ordIdx (p + 1) σ).1
    (inter_eq_cechOpen_ordIdx f V σ)) _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_zsmul (sectionsEquivOfEq f V F hV (ordIdx (p + 1) σ).1
    (inter_eq_cechOpen_ordIdx f V σ)) _ _).trans ?_
  exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z)
    (sectionsEquivOfEq_restrict f V F hV (ordIdx_omit_subset σ j)
      (inter_eq_cechOpen_ordIdx f V _) (inter_eq_cechOpen_ordIdx f V σ)
      (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) σ.1 j) _)

/-- **The degreewise comparison commutes with the differentials.** -/
@[ega "III 1.2.2" "partial"]
public theorem ordCochainToCechTerm_ordD (p : ℕ)
    (s : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf F) p) :
    ordCochainToCechTerm f V F hV (p + 1)
        (CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i))
          (Scheme.Modules.presheaf F) p s) =
      Cech.cechD (eqn f V) Γ(F, V) (p + 1) (ordCochainToCechTerm f V F hV p s) := by
  refine DirectSum.ext fun T => ?_
  obtain ⟨σ, rfl⟩ := exists_ordIdx_eq (p + 1) T
  refine ((cechComponent_ordCochainToCechTerm f V F hV (p + 1) _ σ).trans
    ((sectionsEquivOfEq_ordD f V F hV p s σ).trans ?_)).trans
      (Stacks.LocalCohomology.cechComponent_cechD_ordIndexEquiv (eqn f V)
        (ModuleCat.of Γ(X, V) Γ(F, V)) p (ordCochainToCechTerm f V F hV p s)
        (upIndex (p + 1) σ)).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) •
      Cech.cechι (eqn f V) Γ(F, V) (ordIdx_omit_subset σ j) z)
    (cechComponent_ordCochainToCechTerm f V F hV p s
      ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩).symm

/-! ### Degree zero -/

/-- The Čech open attached to a set of indices of size zero is the whole of `V`. -/
public theorem cechOpen_of_card_zero {T : Finset (Fin c)} (hT : T.card = 0) :
    cechOpen f V T = V := by
  rw [cechOpen, Finset.card_eq_zero.1 hT, Finset.prod_empty, Scheme.basicOpen_one]

/-- There is only one set of indices of size zero. -/
public instance uniqueCardZeroIdx : Unique {t : Finset (Fin c) // t.card = 0} where
  default := ⟨∅, Finset.card_empty⟩
  uniq t := Subtype.ext (Finset.card_eq_zero.1 t.2)

/-- The Čech sign of an element of a one-element set is `+1`: nothing in the set precedes it. -/
public theorem cechSign_of_card_one {T : Finset (Fin c)} (hT : T.card = 1) {k : Fin c}
    (hk : k ∈ T) :
    Cech.cechSign T k = 1 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hT
  rw [Finset.mem_singleton] at hk
  subst hk
  rw [Cech.cechSign, show ({k} : Finset (Fin c)).filter (· < k) = ∅ from by
    ext b; simp +contextual, Finset.card_empty, pow_zero]

variable (D : Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData f F)

/-- The degree-zero term of the algebraic Čech complex is its single summand. -/
public def cechTermZeroIdx :
    Cech.cechMod (eqn f V) Γ(F, V) (default : {t : Finset (Fin c) // t.card = 0}).1
      ≃+ Cech.cechTerm (eqn f V) Γ(F, V) 0 :=
  ((LinearEquiv.piUnique (R := Γ(X, V))
      (fun t : {t : Finset (Fin c) // t.card = 0} =>
        Cech.cechMod (eqn f V) Γ(F, V) t.1)).symm.trans
    (DirectSum.linearEquivFunOnFintype Γ(X, V) {t : Finset (Fin c) // t.card = 0}
      (fun t => Cech.cechMod (eqn f V) Γ(F, V) t.1)).symm).toAddEquiv

omit [F.IsQuasicoherent] in
/-- The component of `cechTermZeroIdx z` at an index set `t` of size zero is the image of `z`
under the transition map `Cech.cechι` along the inclusion of the default index set in `t`. -/
@[simp] theorem cechComponent_cechTermZeroIdx
    (z : Cech.cechMod (eqn f V) Γ(F, V) (default : {t : Finset (Fin c) // t.card = 0}).1)
    (t : {t : Finset (Fin c) // t.card = 0}) :
    Stacks.LocalCohomology.cechComponent (eqn f V) (ModuleCat.of Γ(X, V) Γ(F, V)) 0 t
      (cechTermZeroIdx f V F z) = Cech.cechι (eqn f V) Γ(F, V)
        (le_of_eq (congrArg Subtype.val (Subsingleton.elim (default :
          {t : Finset (Fin c) // t.card = 0}) t))) z := by
  obtain rfl : t = default := Subsingleton.elim _ _
  exact (Stacks.LocalCohomology.cechι_le_refl_apply _ _ _).symm

variable (D : Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData f F)

/-- The sections over `V` of the degree-zero term are the sections of the coefficient module. -/
public def zeroAppEquiv : Γ(D.complex.X 0, V) ≃+ Γ(F, V) where
  toFun := D.zeroIso.hom.app V
  invFun := D.zeroIso.inv.app V
  left_inv z := by
    change (D.zeroIso.hom ≫ D.zeroIso.inv).app V z = z
    rw [D.zeroIso.hom_inv_id]; rfl
  right_inv z := by
    change (D.zeroIso.inv ≫ D.zeroIso.hom).app V z = z
    rw [D.zeroIso.inv_hom_id]; rfl
  map_add' := map_add _

/-- **The degree-zero comparison**: the sections of the degree-zero term over `V` are the
degree-zero term of the algebraic Čech complex. -/
public def zeroEquiv : Γ(D.complex.X 0, V) ≃+ Cech.cechTerm (eqn f V) Γ(F, V) 0 :=
  ((zeroAppEquiv f V F D).trans
    (sectionsEquivOfEq f V F hV (default : {t : Finset (Fin c) // t.card = 0}).1
      (cechOpen_of_card_zero f V (default : {t : Finset (Fin c) // t.card = 0}).2).symm)).trans
    (cechTermZeroIdx f V F)

/-- At an open that is the whole of `V`, the comparison is the constant fraction. -/
public theorem sectionsEquivOfEq_self (T : Finset (Fin c)) (hW : V = cechOpen f V T) (m : Γ(F, V)) :
    sectionsEquivOfEq f V F hV T hW m
      = LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) T) Γ(F, V) m := by
  have h : (Scheme.Modules.presheaf F).map (homOfLE (le_refl V)).op m = m := by
    rw [Subsingleton.elim (homOfLE (le_refl V)) (𝟙 V), op_id,
      (Scheme.Modules.presheaf F).map_id]
    rfl
  exact (congrArg (sectionsEquivOfEq f V F hV T hW) h.symm).trans
    (sectionsEquivOfEq_res f V F hV T hW le_rfl m)

/-- **The degree-zero differential matches.** -/
public theorem ordCochainToCechTerm_differential_zero (x : Γ(D.complex.X 0, V)) :
    ordCochainToCechTerm f V F hV 0 (D.sectionsIso 0 V ((D.complex.d 0 1).app V x))
      = Cech.cechD (eqn f V) Γ(F, V) 0 (zeroEquiv f V F hV D x) := by
  classical
  set m : Γ(F, V) := D.zeroIso.hom.app V x with hm
  refine DirectSum.ext fun T => ?_
  obtain ⟨σ, rfl⟩ := exists_ordIdx_eq 0 T
  have hL : Stacks.LocalCohomology.cechComponent (eqn f V) (ModuleCat.of Γ(X, V) Γ(F, V)) 1
      (ordIdx 0 σ) (ordCochainToCechTerm f V F hV 0
        (D.sectionsIso 0 V ((D.complex.d 0 1).app V x)))
      = LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) (ordIdx 0 σ).1) Γ(F, V) m :=
    (cechComponent_ordCochainToCechTerm f V F hV 0 _ σ).trans
      ((congrArg (sectionsEquivOfEq f V F hV (ordIdx 0 σ).1
          (inter_eq_cechOpen_ordIdx f V σ)) (D.differential_zero V x σ)).trans
        (sectionsEquivOfEq_res f V F hV (ordIdx 0 σ).1
          (inter_eq_cechOpen_ordIdx f V σ) _ m))
  obtain ⟨k, hk⟩ : ∃ k, k ∈ (ordIdx 0 σ).1 :=
    ⟨σ.1 0, Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (ordIdx 0 σ).2
  have hR : Stacks.LocalCohomology.cechComponent (eqn f V) (ModuleCat.of Γ(X, V) Γ(F, V)) 1
      (ordIdx 0 σ) (Cech.cechD (eqn f V) Γ(F, V) 0 (zeroEquiv f V F hV D x))
      = LocalizedModule.mkLinearMap (Cech.cechSub (eqn f V) (ordIdx 0 σ).1) Γ(F, V) m := by
    rw [Stacks.LocalCohomology.cechComponent_cechD,
      Finset.sum_eq_single_of_mem (⟨k, hk⟩ : {b // b ∈ (ordIdx 0 σ).1})
        (Finset.mem_attach _ _) (fun b _ hb => absurd (Subtype.ext
          ((Finset.mem_singleton.1 (ha ▸ b.2)).trans
            (Finset.mem_singleton.1 (ha ▸ hk)).symm)) hb),
      cechSign_of_card_one (ordIdx 0 σ).2 hk, one_smul,
      show zeroEquiv f V F hV D x = cechTermZeroIdx f V F
          (sectionsEquivOfEq f V F hV (default : {t : Finset (Fin c) // t.card = 0}).1
            (cechOpen_of_card_zero f V
              (default : {t : Finset (Fin c) // t.card = 0}).2).symm
            (zeroAppEquiv f V F D x)) from rfl,
      cechComponent_cechTermZeroIdx, Cech.cechι_cechι, sectionsEquivOfEq_self,
      Cech.cechι_mk]
    rfl
  exact hL.trans hR.symm

/-! ### The comparison of complexes -/

/-- The degreewise comparison of the complex of sections over `V` with the algebraic Čech
complex: `Γ(ℱ, V)` in degree zero, and the ordered Čech cochains in positive degrees. -/
public def complexXIso : ∀ n : ℕ,
    (((ExtendedAlternatingCech.moduleSectionsFunctor V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.complex).X n ≅
      (((forget₂ (ModuleCat.{u} Γ(X, V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (_root_.Cech.cechComplex (eqn f V) Γ(F, V))).X n
  | 0 => (zeroEquiv f V F hV D).toAddCommGrpIso
  | (p + 1) => ((D.sectionsIso p V).trans (ordCochainEquivCechTerm f V F hV p)).toAddCommGrpIso

/-- **The complex of sections over an affine open is the algebraic extended alternating Čech
complex of the restricted equations with coefficients in the sections of `ℱ`.** -/
public def complexIso :
    ((ExtendedAlternatingCech.moduleSectionsFunctor V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.complex ≅
      ((forget₂ (ModuleCat.{u} Γ(X, V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (_root_.Cech.cechComplex (eqn f V) Γ(F, V)) :=
  HomologicalComplex.Hom.isoOfComponents (complexXIso f V F hV D) (by
    rintro i j (rfl : i + 1 = j)
    rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d,
      _root_.Cech.cechComplex_d]
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    cases i with
    | zero => exact (ordCochainToCechTerm_differential_zero f V F hV D x).symm
    | succ p =>
        exact (ordCochainToCechTerm_ordD f V F hV p (D.sectionsIso p V x)).symm.trans
          (congrArg (ordCochainToCechTerm f V F hV (p + 1))
            (D.differential_succ p V x).symm))

end Stacks.Perfect.AffineCechSections

end
