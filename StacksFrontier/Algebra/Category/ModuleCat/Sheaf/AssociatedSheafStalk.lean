module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkBaseChange

/-!
# The stalks of the sheaf associated to a module

Let `(X, 𝒪_X)` be a ringed space, `α : A → Γ(X, 𝒪_X)` a ring homomorphism and `M` an
`A`-module.  The sheaf `ℱ_M` of `𝒪_X`-modules associated to `M` and `α`
(`Stacks.AssociatedSheaf.associatedSheaf`, construction (3) of Stacks 01BH) is the
sheafification of the presheaf `U ↦ 𝒪_X(U) ⊗_A M`.  This file computes its stalks:

`(ℱ_M)_x ≅ 𝒪_{X,x} ⊗_A M`.

## Main definitions

* `Stacks.AssociatedSheaf.sectionAlgebra` and `Stacks.AssociatedSheaf.stalkAlgebra`: the
  `A`-algebra structures on `𝒪_X(U)` and on `𝒪_{X,x}` through which the two tensor products are
  taken; they are `α` followed by restriction, respectively by the germ map.
* `Stacks.AssociatedSheaf.germLinearMap`: the germ map `𝒪_X(U) → 𝒪_{X,x}` as an `A`-linear map.
* `Stacks.AssociatedSheaf.assocTmul` and `Stacks.AssociatedSheaf.assocGerm`: the pure tensor
  `s ⊗ m` as a section of the associated presheaf over `U`, and the germ map at `x` of the
  associated presheaf as an additive map.
* `Stacks.AssociatedSheaf.toPresheafStalk`: the canonical additive map `M → (ℱ_M^{pre})_x`
  sending `m` to the germ of `1 ⊗ m`.
* `Stacks.AssociatedSheaf.presheafStalkFwd` and `Stacks.AssociatedSheaf.presheafStalkBack`: the
  two comparison maps between the stalk of `U ↦ 𝒪_X(U) ⊗_A M` and `𝒪_{X,x} ⊗_A M`.  The first
  sends the germ of `s ⊗ m` to `(germ s) ⊗ m`, the second sends `r ⊗ m` to `r • ι(m)`.
* `Stacks.AssociatedSheaf.presheafStalkAddEquiv` and
  `Stacks.AssociatedSheaf.presheafStalkLinearEquiv`: the resulting identification of the stalk
  of the *presheaf* `U ↦ 𝒪_X(U) ⊗_A M` with `𝒪_{X,x} ⊗_A M`, additively and `𝒪_{X,x}`-linearly.
* `Stacks.AssociatedSheaf.sheafificationStalkAddEquiv`: the identification of the stalk of that
  presheaf with the stalk of its sheafification, which is `ℱ_M`.
* `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`: the composite of the two, which is the
  statement above.

## Main results

* `Stacks.AssociatedSheaf.germ_assocTmul`: the one computation the comparison rests on — the
  germ of `s ⊗ m` is `(germ s) • ι(m)`.  Both round trips reduce to it.
* `Stacks.AssociatedSheaf.isIso_stalkFunctor_map_associatedSheafUnit`: sheafification of
  presheaves of modules does not change stalks, at the associated presheaf.
* `Stacks.AssociatedSheaf.nonempty_associatedSheafStalkAddEquiv`: the existence form of
  `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`.

## Implementation notes

The comparison is built as a pair of mutually inverse maps rather than by invoking a general
interchange of tensor products with filtered colimits.  The forward map is the descent of the
cocone whose leg over a neighbourhood `U` of `x` is `Stacks.AssociatedSheaf.germLinearMap`
tensored with the identity of `M`; the backward map is `TensorProduct.liftAddHom` of
`(r, m) ↦ r • ι(m)`, which needs no universal property of `𝒪_{X,x}`.  That is the point of
writing it that way: `𝒪_{X,x}` is a colimit of *rings*, so its universal property produces ring
homomorphisms, not the additive maps that a tensor product's universal property consumes.  With
the backward map a scalar multiplication instead, both round trips become
`Stacks.AssociatedSheaf.germ_assocTmul` read in the two directions, and no module structure
over `A` on the stalk is needed anywhere.

Every statement about a section of the associated presheaf is phrased through
`Stacks.SitePointBaseChange.cofTmul`, as `Stacks.AssociatedSheaf.assocTmul`, rather than through
`⊗ₜ` directly, and every germ through the bundled additive map
`Stacks.AssociatedSheaf.assocGerm`.  The reason in both cases is that the base ring of the
tensor product is `(constantRingPresheaf X A)(U)` and its module is `(constantModulePresheaf X
M)(U)`, which are `A` and `M` only up to unfolding: a `⊗ₜ[A]` written in a statement carries
different instances from the one the elaborator produces for the presheaf's own sections, and
`rw` then reports the goal as not type-correct under the implicit transparency level.

The scalar multiplication of `𝒪_{X,x}` on the stalk is Mathlib's module structure on the stalk
of a presheaf of modules, whose characterising equation is `PresheafOfModules.germ_smul`.

Everything is stated at a single universe: that module structure is stated for a presheaf of
modules over a presheaf of rings on a space all living in one universe, the filtered colimit
computing the stalk being indexed by the opens of the space.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3): the stalk
  of the sheaf associated to a module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.AssociatedSheaf

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (α : A →+* X.presheaf.obj (op ⊤)) (M : ModuleCat.{u} A) (x : X.carrier)

/-! ### The two `A`-algebra structures -/

/-- **`𝒪_X(U)` as an `A`-algebra**, through `α` followed by restriction from `X` to `U`.  This
is the algebra structure over which the sections `𝒪_X(U) ⊗_A M` of the associated presheaf are
formed. -/
abbrev sectionAlgebra (U : Opens X.carrier) : Algebra A (X.presheaf.obj (op U)) :=
  ((globalSectionsMap X α).app (op U)).hom.toAlgebra

/-- **`𝒪_{X,x}` as an `A`-algebra**, through `α` followed by the germ map at `x`. -/
abbrev stalkAlgebra : Algebra A (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp α).toAlgebra

/-- The germ map carries the structural map of `Stacks.AssociatedSheaf.sectionAlgebra` to that
of `Stacks.AssociatedSheaf.stalkAlgebra`: both are `α` followed by a germ, taken over `U` in
one case and over `X` in the other, and germs are invariant under restriction. -/
theorem germ_algebraMap (U : Opens X.carrier) (hx : x ∈ U) (a : A) :
    letI := sectionAlgebra X α U
    letI := stalkAlgebra X α x
    (X.presheaf.germ U x hx).hom (algebraMap A (X.presheaf.obj (op U)) a) =
      algebraMap A (X.presheaf.stalk x) a :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top (a := U))) x hx (α a)

/-- **The germ map as an `A`-linear map `𝒪_X(U) → 𝒪_{X,x}`.**  It is `A`-linear because it is a
ring homomorphism commuting with the two structural maps, which is
`Stacks.AssociatedSheaf.germ_algebraMap`. -/
def germLinearMap (U : Opens X.carrier) (hx : x ∈ U) :
    letI := sectionAlgebra X α U
    letI := stalkAlgebra X α x
    X.presheaf.obj (op U) →ₗ[A] X.presheaf.stalk x :=
  letI := sectionAlgebra X α U
  letI := stalkAlgebra X α x
  { toFun := (X.presheaf.germ U x hx).hom
    map_add' := map_add _
    map_smul' := fun a s => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, germ_algebraMap X α x U hx a]
      rfl }

/-! ### Pure tensor sections and germs of the associated presheaf -/

/-- **The pure tensor `s ⊗ m`** as a section of the associated presheaf `U ↦ 𝒪_X(U) ⊗_A M`.
This is `Stacks.SitePointBaseChange.cofTmul` for the extension of scalars along
`Stacks.AssociatedSheaf.globalSectionsMap`, of which the associated presheaf is an instance. -/
abbrev assocTmul (U : Opens X.carrier) (s : X.presheaf.obj (op U)) (m : M) :
    ToType ((associatedPresheaf X α M).obj (op U)) :=
  Stacks.SitePointBaseChange.cofTmul (globalSectionsMap X α) (constantModulePresheaf X M) U s m

/-- **The germ map at `x` of the associated presheaf**, as an additive map.  Bundling it keeps
`map_zero` and `map_add` applicable to it syntactically. -/
def assocGerm (U : Opens X.carrier) (hx : x ∈ U) :
    ToType ((associatedPresheaf X α M).obj (op U)) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) :=
  AddCommGrpCat.Hom.hom (TopCat.Presheaf.germ (associatedPresheaf X α M).presheaf U x hx)

/-- `Stacks.AssociatedSheaf.assocGerm` is the germ map. -/
theorem assocGerm_apply (U : Opens X.carrier) (hx : x ∈ U)
    (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    assocGerm X α M x U hx t =
      ConcreteCategory.hom (TopCat.Presheaf.germ (associatedPresheaf X α M).presheaf U x hx) t :=
  rfl

/-- **Germs are invariant under restriction**, for the associated presheaf. -/
theorem assocGerm_restrict {U V : Opens X.carrier} (g : V ⟶ U) (hxV : x ∈ V) (hxU : x ∈ U)
    (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    assocGerm X α M x V hxV ((associatedPresheaf X α M).restrictₛₗ g.op t) =
      assocGerm X α M x U hxU t := by
  refine Eq.trans (congrArg (assocGerm X α M x V hxV)
    (PresheafOfModules.presheaf_map_apply_coe (associatedPresheaf X α M) g.op t).symm) ?_
  exact TopCat.Presheaf.germ_res_apply (associatedPresheaf X α M).presheaf g x hxV t

/-- **The germ map is semilinear over the germ map of `𝒪_X`.**  This is Mathlib's module
structure on the stalk of a presheaf of modules, at the associated presheaf. -/
theorem assocGerm_smul (U : Opens X.carrier) (hx : x ∈ U) (r : X.presheaf.obj (op U))
    (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    assocGerm X α M x U hx (r • t) =
      (X.presheaf.germ U x hx).hom r • assocGerm X α M x U hx t :=
  PresheafOfModules.germ_smul (R := X.presheaf) (associatedPresheaf X α M) x U hx r t

/-! ### The canonical map `M → (ℱ_M^{pre})_x` -/

/-- **The canonical additive map `M → (U ↦ 𝒪_X(U) ⊗_A M)_x`**, sending `m` to the germ of the
section `1 ⊗ m` over the whole space. -/
def toPresheafStalk :
    M →+ ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (associatedPresheaf X α M).presheaf x) :=
  (assocGerm X α M x ⊤ trivial).comp
    (Stacks.SitePointBaseChange.oneTmul (globalSectionsMap X α) (constantModulePresheaf X M) ⊤)

/-- `Stacks.AssociatedSheaf.toPresheafStalk` is the germ of `1 ⊗ m` over *any* neighbourhood of
`x`, restriction of `1 ⊗ m` being `1 ⊗ m`. -/
theorem toPresheafStalk_eq_germ (U : Opens X.carrier) (hx : x ∈ U) (m : M) :
    toPresheafStalk X α M x m =
      assocGerm X α M x U hx (assocTmul X α M U (1 : X.presheaf.obj (op U)) m) := by
  refine Eq.trans (assocGerm_restrict X α M x (homOfLE (le_top (a := U))) hx trivial
    (assocTmul X α M ⊤ (1 : X.presheaf.obj (op ⊤)) m)).symm ?_
  refine congrArg (assocGerm X α M x U hx) ?_
  refine Eq.trans (Stacks.SitePointBaseChange.res_cofTmul (globalSectionsMap X α)
    (constantModulePresheaf X M) (homOfLE (le_top (a := U)))
    (1 : X.presheaf.obj (op ⊤)) m) ?_
  exact congrArg (fun s => assocTmul X α M U s m)
    (map_one (X.presheaf.map (homOfLE (le_top (a := U))).op).hom)

/-- **The computation the comparison rests on.**  The germ of `s ⊗ m` over a neighbourhood `U`
of `x` is `(germ s) • ι(m)`, for `ι` the canonical map of
`Stacks.AssociatedSheaf.toPresheafStalk`.  Both round trips of the comparison are this identity,
read in the two directions. -/
theorem germ_assocTmul (U : Opens X.carrier) (hx : x ∈ U) (s : X.presheaf.obj (op U)) (m : M) :
    assocGerm X α M x U hx (assocTmul X α M U s m) =
      (X.presheaf.germ U x hx).hom s • toPresheafStalk X α M x m := by
  refine Eq.trans (congrArg (assocGerm X α M x U hx)
    (Eq.trans (congrArg (fun y => assocTmul X α M U y m) (mul_one s).symm)
      (Stacks.SitePointBaseChange.smul_cofTmul (globalSectionsMap X α)
        (constantModulePresheaf X M) U s (1 : X.presheaf.obj (op U)) m).symm)) ?_
  refine Eq.trans (assocGerm_smul X α M x U hx s
    (assocTmul X α M U (1 : X.presheaf.obj (op U)) m)) ?_
  exact congrArg ((X.presheaf.germ U x hx).hom s • ·) (toPresheafStalk_eq_germ X α M x U hx m).symm

/-- **Scalars of `A` move across the canonical map.**  `ι(a • m)` is `a` acting on `ι(m)`
through the germ of `α`, which is the structural map of
`Stacks.AssociatedSheaf.stalkAlgebra`. -/
theorem toPresheafStalk_smul (a : A) (m : M) :
    letI := stalkAlgebra X α x
    toPresheafStalk X α M x (a • m) =
      algebraMap A (X.presheaf.stalk x) a • toPresheafStalk X α M x m := by
  let := sectionAlgebra X α ⊤
  let := stalkAlgebra X α x
  refine Eq.trans (congrArg (assocGerm X α M x ⊤ trivial)
    (Stacks.SitePointBaseChange.cofTmul_one_smul (globalSectionsMap X α)
      (constantModulePresheaf X M) ⊤ a m)) ?_
  refine Eq.trans (germ_assocTmul X α M x ⊤ trivial
    (((globalSectionsMap X α).app (op ⊤)).hom a) m) ?_
  exact congrArg (· • toPresheafStalk X α M x m) (germ_algebraMap X α x ⊤ trivial a)

/-! ### The forward comparison map -/

/-- The leg over a neighbourhood `U` of `x` of the cocone defining the forward comparison: the
germ map of `𝒪_X` tensored with the identity of `M`. -/
def presheafStalkLeg (U : Opens X.carrier) (hx : x ∈ U) :
    letI := stalkAlgebra X α x
    ToType ((associatedPresheaf X α M).obj (op U)) →+ (X.presheaf.stalk x ⊗[A] M) :=
  letI := sectionAlgebra X α U
  letI := stalkAlgebra X α x
  (LinearMap.rTensor M (germLinearMap X α x U hx)).toAddMonoidHom

/-- The leg of the forward cocone sends `s ⊗ m` to `(germ s) ⊗ m`. -/
theorem presheafStalkLeg_assocTmul (U : Opens X.carrier) (hx : x ∈ U)
    (s : X.presheaf.obj (op U)) (m : M) :
    letI := stalkAlgebra X α x
    presheafStalkLeg X α M x U hx (assocTmul X α M U s m) =
      (X.presheaf.germ U x hx).hom s ⊗ₜ[A] m :=
  rfl

/-- The legs of the forward cocone are compatible with restriction, germs being invariant under
restriction.  This is the cocone condition. -/
theorem presheafStalkLeg_restrict {U V : Opens X.carrier} (g : V ⟶ U) (hxV : x ∈ V)
    (hxU : x ∈ U) (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    presheafStalkLeg X α M x V hxV ((associatedPresheaf X α M).restrictₛₗ g.op t) =
      presheafStalkLeg X α M x U hxU t := by
  let := stalkAlgebra X α x
  induction t using Stacks.SitePointBaseChange.cof_induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul s m =>
    refine Eq.trans (congrArg (presheafStalkLeg X α M x V hxV)
      (Stacks.SitePointBaseChange.res_cofTmul (globalSectionsMap X α)
        (constantModulePresheaf X M) g s m)) ?_
    refine Eq.trans (presheafStalkLeg_assocTmul X α M x V hxV
      ((X.presheaf.map g.op).hom s) m) ?_
    refine Eq.trans ?_ (presheafStalkLeg_assocTmul X α M x U hxU s m).symm
    exact congrArg (· ⊗ₜ[A] m) (TopCat.Presheaf.germ_res_apply X.presheaf g x hxV s)

/-- The cocone over the stalk diagram of the associated presheaf with apex `𝒪_{X,x} ⊗_A M`
whose legs are `Stacks.AssociatedSheaf.presheafStalkLeg`. -/
def presheafStalkCocone :
    letI := stalkAlgebra X α x
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ (associatedPresheaf X α M).presheaf) :=
  letI := stalkAlgebra X α x
  { pt := AddCommGrpCat.of (X.presheaf.stalk x ⊗[A] M)
    ι :=
      { app := fun j => AddCommGrpCat.ofHom (presheafStalkLeg X α M x j.unop.1 j.unop.2)
        naturality := fun j k f =>
          AddCommGrpCat.hom_ext (AddMonoidHom.ext fun t =>
            presheafStalkLeg_restrict X α M x ((OpenNhds.inclusion x).map f.unop)
              k.unop.2 j.unop.2 t) } }

/-- **The forward comparison `(U ↦ 𝒪_X(U) ⊗_A M)_x → 𝒪_{X,x} ⊗_A M`**, the descent of
`Stacks.AssociatedSheaf.presheafStalkCocone`. -/
def presheafStalkFwd :
    letI := stalkAlgebra X α x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) →+
      (X.presheaf.stalk x ⊗[A] M) :=
  letI := stalkAlgebra X α x
  AddCommGrpCat.Hom.hom (Limits.colimit.desc _ (presheafStalkCocone X α M x))

/-- The forward comparison sends the germ of a section of the associated presheaf to the value
of the corresponding leg of `Stacks.AssociatedSheaf.presheafStalkCocone`. -/
theorem presheafStalkFwd_assocGerm (U : Opens X.carrier) (hx : x ∈ U)
    (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    presheafStalkFwd X α M x (assocGerm X α M x U hx t) =
      presheafStalkLeg X α M x U hx t :=
  congrArg (fun φ => AddCommGrpCat.Hom.hom φ t)
    (Limits.colimit.ι_desc (presheafStalkCocone X α M x) (op ⟨U, hx⟩))

/-! ### The backward comparison map -/

/-- The additive map `𝒪_{X,x} →+ M →+ (ℱ_M^{pre})_x` sending `r` and `m` to `r • ι(m)`, out of
which the backward comparison is lifted. -/
def presheafStalkBackBilin :
    X.presheaf.stalk x →+
      (M →+ ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x)) where
  toFun r :=
    { toFun := fun m => r • toPresheafStalk X α M x m
      map_zero' := Eq.trans (congrArg (r • ·) (map_zero (toPresheafStalk X α M x)))
        (smul_zero r)
      map_add' := fun m₁ m₂ => Eq.trans
        (congrArg (r • ·) (map_add (toPresheafStalk X α M x) m₁ m₂)) (smul_add r _ _) }
  map_zero' := AddMonoidHom.ext fun _ => zero_smul _ _
  map_add' r₁ r₂ := AddMonoidHom.ext fun _ => add_smul r₁ r₂ _

/-- **The backward comparison `𝒪_{X,x} ⊗_A M → (U ↦ 𝒪_X(U) ⊗_A M)_x`**, sending `r ⊗ m` to
`r • ι(m)`.  It is balanced over `A` because `ι(a • m)` is `a` acting on `ι(m)` through the germ
of `α`, which is `Stacks.AssociatedSheaf.toPresheafStalk_smul`. -/
def presheafStalkBack :
    letI := stalkAlgebra X α x
    (X.presheaf.stalk x ⊗[A] M) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) :=
  letI := stalkAlgebra X α x
  TensorProduct.liftAddHom (presheafStalkBackBilin X α M x) fun a r m => by
    refine Eq.trans (congrArg (· • toPresheafStalk X α M x m) (Algebra.smul_def a r)) ?_
    refine Eq.trans (mul_smul (algebraMap A (X.presheaf.stalk x) a) r _) ?_
    refine Eq.trans (smul_comm (algebraMap A (X.presheaf.stalk x) a) r _) ?_
    exact congrArg (r • ·) (toPresheafStalk_smul X α M x a m).symm

/-- The backward comparison sends `r ⊗ m` to `r • ι(m)`. -/
theorem presheafStalkBack_tmul (r : X.presheaf.stalk x) (m : M) :
    letI := stalkAlgebra X α x
    presheafStalkBack X α M x (r ⊗ₜ[A] m) = r • toPresheafStalk X α M x m :=
  rfl

/-! ### The two round trips -/

/-- **The backward comparison undoes a leg of the forward cocone.**  On a section over a
neighbourhood `U` of `x`, the composite of the leg over `U` with the backward comparison is the
germ map.  By `Stacks.SitePointBaseChange.cof_induction` it suffices to check this on pure
tensors, where it is `Stacks.AssociatedSheaf.germ_assocTmul`. -/
theorem presheafStalkBack_presheafStalkLeg (U : Opens X.carrier) (hx : x ∈ U)
    (t : ToType ((associatedPresheaf X α M).obj (op U))) :
    presheafStalkBack X α M x (presheafStalkLeg X α M x U hx t) = assocGerm X α M x U hx t := by
  let := stalkAlgebra X α x
  induction t using Stacks.SitePointBaseChange.cof_induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul s m =>
    refine Eq.trans (congrArg (presheafStalkBack X α M x)
      (presheafStalkLeg_assocTmul X α M x U hx s m)) ?_
    refine Eq.trans (presheafStalkBack_tmul X α M x ((X.presheaf.germ U x hx).hom s) m) ?_
    exact (germ_assocTmul X α M x U hx s m).symm

/-- The backward comparison is a left inverse of the forward one. -/
theorem presheafStalkBack_presheafStalkFwd
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (associatedPresheaf X α M).presheaf x)) :
    presheafStalkBack X α M x (presheafStalkFwd X α M x ξ) = ξ := by
  obtain ⟨U, hx, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (associatedPresheaf X α M).presheaf ξ
  have h : assocGerm X α M x U hx t = ξ := ht
  exact Eq.trans (congrArg (fun y => presheafStalkBack X α M x (presheafStalkFwd X α M x y))
      h.symm)
    (Eq.trans (congrArg (presheafStalkBack X α M x)
        (presheafStalkFwd_assocGerm X α M x U hx t))
      (Eq.trans (presheafStalkBack_presheafStalkLeg X α M x U hx t) h))

/-- The backward comparison is a right inverse of the forward one. -/
theorem presheafStalkFwd_presheafStalkBack :
    letI := stalkAlgebra X α x
    ∀ z : X.presheaf.stalk x ⊗[A] M,
      presheafStalkFwd X α M x (presheafStalkBack X α M x z) = z := by
  let := stalkAlgebra X α x
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul r m =>
    obtain ⟨U, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    subst hs
    refine Eq.trans (congrArg (presheafStalkFwd X α M x)
      (Eq.trans (presheafStalkBack_tmul X α M x ((X.presheaf.germ U x hx).hom s) m)
        (germ_assocTmul X α M x U hx s m).symm)) ?_
    refine Eq.trans (presheafStalkFwd_assocGerm X α M x U hx (assocTmul X α M U s m)) ?_
    exact presheafStalkLeg_assocTmul X α M x U hx s m

/-- **The stalk of the presheaf `U ↦ 𝒪_X(U) ⊗_A M` is `𝒪_{X,x} ⊗_A M`.**  The content is that
the tensor product with the fixed `A`-module `M` commutes with the filtered colimit computing
the stalk; no sheaf condition is used. -/
def presheafStalkAddEquiv :
    letI := stalkAlgebra X α x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) ≃+
      (X.presheaf.stalk x ⊗[A] M) :=
  letI := stalkAlgebra X α x
  AddEquiv.ofBijective (presheafStalkFwd X α M x)
    ⟨Function.HasLeftInverse.injective
        ⟨presheafStalkBack X α M x, presheafStalkBack_presheafStalkFwd X α M x⟩,
      Function.HasRightInverse.surjective
        ⟨presheafStalkBack X α M x, presheafStalkFwd_presheafStalkBack X α M x⟩⟩

/-- **The backward comparison is `𝒪_{X,x}`-linear.**  On `r' ⊗ m` both sides are
`(r * r') • ι(m)`. -/
theorem presheafStalkBack_smul (r : X.presheaf.stalk x) :
    letI := stalkAlgebra X α x
    ∀ z : X.presheaf.stalk x ⊗[A] M,
      presheafStalkBack X α M x (r • z) = r • presheafStalkBack X α M x z := by
  let := stalkAlgebra X α x
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
  | tmul r' m =>
    refine Eq.trans (congrArg (presheafStalkBack X α M x)
      (TensorProduct.smul_tmul' r r' m)) ?_
    refine Eq.trans (presheafStalkBack_tmul X α M x (r * r') m) ?_
    refine Eq.trans (mul_smul r r' (toPresheafStalk X α M x m)) ?_
    exact congrArg (r • ·) (presheafStalkBack_tmul X α M x r' m).symm

/-- `Stacks.AssociatedSheaf.presheafStalkBack` as an `𝒪_{X,x}`-linear map. -/
def presheafStalkBackLinear :
    letI := stalkAlgebra X α x
    (X.presheaf.stalk x ⊗[A] M) →ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) :=
  letI := stalkAlgebra X α x
  { toFun := presheafStalkBack X α M x
    map_add' := map_add _
    map_smul' := presheafStalkBack_smul X α M x }

/-- **The stalk of the presheaf `U ↦ 𝒪_X(U) ⊗_A M` is `𝒪_{X,x} ⊗_A M` as an
`𝒪_{X,x}`-module.**  This is `Stacks.AssociatedSheaf.presheafStalkAddEquiv` together with the
`𝒪_{X,x}`-linearity recorded in `Stacks.AssociatedSheaf.presheafStalkBack_smul`. -/
def presheafStalkLinearEquiv :
    letI := stalkAlgebra X α x
    (X.presheaf.stalk x ⊗[A] M) ≃ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) :=
  letI := stalkAlgebra X α x
  LinearEquiv.ofBijective (presheafStalkBackLinear X α M x)
    ⟨Function.HasLeftInverse.injective
        ⟨presheafStalkFwd X α M x, presheafStalkFwd_presheafStalkBack X α M x⟩,
      Function.HasRightInverse.surjective
        ⟨presheafStalkFwd X α M x, presheafStalkBack_presheafStalkFwd X α M x⟩⟩

/-! ### Sheafification does not change the stalk -/

/-- The unit of sheafification of presheaves of modules, from the associated presheaf to the
underlying presheaf of the associated sheaf. -/
abbrev associatedSheafUnit :
    associatedPresheaf X α M ⟶
      (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (structureSheafRing X).obj)).obj
        (associatedSheaf X α M) :=
  letI := hasModuleSheafify.{u, u} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, u} X
  (PresheafOfModules.sheafificationAdjunction.{u}
    (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).unit.app (associatedPresheaf X α M)

/-- **Sheafification does not change stalks.**  The stalk functor on presheaves of abelian
groups carries `Stacks.AssociatedSheaf.associatedSheafUnit` to an isomorphism: that unit is, on
underlying presheaves of abelian groups, the unit `CategoryTheory.toSheafify` of sheafification
of presheaves of abelian groups. -/
theorem isIso_stalkFunctor_map_associatedSheafUnit :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (associatedSheafUnit X α M))) := by
  let := hasModuleSheafify.{u, u} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, u} X
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (associatedPresheaf X α M).presheaf

/-- **The stalk of the associated presheaf is the stalk of the associated sheaf.**  This is
`Stacks.AssociatedSheaf.isIso_stalkFunctor_map_associatedSheafUnit` read as a bijection. -/
def sheafificationStalkAddEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedSheaf X α M).val.presheaf x) :=
  letI := isIso_stalkFunctor_map_associatedSheafUnit X α M x
  AddEquiv.ofBijective
    (AddCommGrpCat.Hom.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (associatedSheafUnit X α M))))
    (ConcreteCategory.bijective_of_isIso (C := AddCommGrpCat.{u}) _)

/-! ### The stalk of the associated sheaf -/

/-- **Stacks 01BH, clause (3): `(ℱ_M)_x ≅ 𝒪_{X,x} ⊗_A M`.**  The stalk at a point `x` of the
sheaf of `𝒪_X`-modules associated to an `A`-module `M` and a ring map `α : A → Γ(X, 𝒪_X)` is the
base change of `M` to the stalk of the structure sheaf.

The identification is the composite of
`Stacks.AssociatedSheaf.sheafificationStalkAddEquiv`, which says that sheafification does not
change stalks, with `Stacks.AssociatedSheaf.presheafStalkAddEquiv`, which computes the stalk of
the presheaf `U ↦ 𝒪_X(U) ⊗_A M`. -/
def associatedSheafStalkAddEquiv :
    letI := stalkAlgebra X α x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedSheaf X α M).val.presheaf x) ≃+
      (X.presheaf.stalk x ⊗[A] M) :=
  letI := stalkAlgebra X α x
  (sheafificationStalkAddEquiv X α M x).symm.trans (presheafStalkAddEquiv X α M x)

/-- The existence form of `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`. -/
theorem nonempty_associatedSheafStalkAddEquiv :
    letI : Algebra A (ToType (X.presheaf.stalk x)) :=
      ((X.presheaf.germ ⊤ x trivial).hom.comp α).toAlgebra
    Nonempty (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedSheaf X α M).val.presheaf x) ≃+
      (ToType (X.presheaf.stalk x) ⊗[A] M)) :=
  ⟨associatedSheafStalkAddEquiv X α M x⟩

end Stacks.AssociatedSheaf

end

end
