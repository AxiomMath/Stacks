module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageProductSubmodule

/-!
# An extension of scalars multiplies out no more than its unit sections do

Let `α : R₁ ⟶ R` be a morphism of sheaves of rings on a site, let `M` be a sheaf of
`R₁`-modules and let `A` be a sheaf of `R`-modules receiving a map
`u : M ⟶ (restrictScalars α) A` which exhibits `A` as the extension of scalars `R ⊗_{R₁} M`,
in the only sense used here: a map out of `A` whose composite with `u` vanishes is zero. Let
`a : A ⟶ R` be a map into the unit module and let `F` be a sheaf of `R`-modules.

The submodule of `F` that the sections of `A` multiply out, i.e.
`Stacks.SheafOfModules.imageProductSubmodule a F`, is then **already** multiplied out by the
much smaller family of sections `a(u(j))`, `j` a section of `M`:

`a(A)·F = {a(u(j))}·F`.

For `A = f^*G` the extension of scalars of an inverse image this is the statement that `f^*G` is
generated, as a sheaf of modules, by the image of `f^{-1}G` — the formal replacement for the
sentence "a section of `f^*G` is locally a sum of pure tensors `o ⊗ j`, and `a(o ⊗ j) = o·a(j)`".

## Main definitions

* `Stacks.SheafOfModules.ringValue`: a section of `A`, read in the sheaf of rings through a map
  of `A` into the unit module.
* `Stacks.SheafOfModules.unitImageSections`: the family of sections `a(u(j))`.

## Main results

* `Stacks.SheafOfModules.imageProductSubmodule_eq_unitImageSections`: the displayed equality.
* `Stacks.SheafOfModules.restrictScalars_unit_cancel_zero`: the hypothesis on `u` holds for the
  unit of any adjunction whose right adjoint is restriction of scalars along `α`, which is what
  extension of scalars is defined to be.

## Implementation notes

The proof is the one that avoids pure tensors, and so avoids every description of the
construction of the extension of scalars. Write `P` for the right-hand side and consider

`S = {z : A | a(z|_V) • m ∈ P(V) for every restriction z|_V and every section m of F}`.

This is a sheaf submodule of `A` — the quantification over all restrictions makes it stable
under restriction, commutativity of the scalars is not needed because `a` is linear, and its
membership condition is local because that of `P` is. It contains every section `u(j)`, since
`a(u(j)|_V) = a(u(j|_V))` by naturality of `u`, and the products of those sections with the
sections of `F` are exactly the generators of `P`. A map out of `A` killing `S` therefore kills
every `u(j)`, so its composite with `u` vanishes, so it is zero: the inclusion of `S` is an
epimorphism. Being also a monomorphism of sheaves of modules it is locally surjective, and
locality of the membership condition of `S` upgrades that to `S = A`, which is the statement.

The hypothesis on `u` is stated as the cancellation property rather than as an adjunction so
that it can be supplied by whichever of the library's several forms of extension of scalars is
at hand, and so that the identification of `A` with a functor applied to `M` need not be made
on the nose.

Sections of the unit module are read in the sheaf of rings by the function
`Stacks.SheafOfModules.ringValue` rather than by a type ascription. The carriers are the same
type, but only after unfolding `SheafOfModules.unit`, so an ascription elaborates to a
`have`-binding that no rewrite can see through; naming the reading once, with its additivity,
linearity and naturality as lemmas, is what keeps the calculations below legible.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ) — extension of scalars
  for sheaves of modules is left adjoint to restriction of scalars.
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6) — the pullback of a
  sheaf of modules is the extension of scalars of its inverse image.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A F : SheafOfModules.{u} R}

/-! ### Reading a section of `A` in the sheaf of rings -/

/-- A section of `A`, read as a section of the sheaf of rings through a map `a : A ⟶ R` into the
unit module. -/
noncomputable def ringValue (a : A ⟶ SheafOfModules.unit R) (U : Cᵒᵖ) (z : A.val.obj U) :
    R.obj.obj U :=
  a.val.app U z

/-- The reading `ringValue a U` sends `0` to `0`. -/
@[simp]
lemma ringValue_zero (a : A ⟶ SheafOfModules.unit R) (U : Cᵒᵖ) :
    ringValue a U (0 : A.val.obj U) = 0 :=
  map_zero (ConcreteCategory.hom (a.val.app U))

/-- The reading `ringValue a U` is additive. -/
@[simp]
lemma ringValue_add (a : A ⟶ SheafOfModules.unit R) (U : Cᵒᵖ) (z z' : A.val.obj U) :
    ringValue a U (z + z') = ringValue a U z + ringValue a U z' :=
  map_add (ConcreteCategory.hom (a.val.app U)) z z'

/-- The reading `ringValue a U` is `R(U)`-linear: `ringValue a U (r • z) = r * ringValue a U z`. -/
@[simp]
lemma ringValue_smul (a : A ⟶ SheafOfModules.unit R) (U : Cᵒᵖ) (r : R.obj.obj U)
    (z : A.val.obj U) : ringValue a U (r • z) = r * ringValue a U z :=
  map_smul (ConcreteCategory.hom (a.val.app U)) r z

/-- Reading a restricted section is restricting the reading: naturality of `a`. -/
lemma ringValue_restrictₛₗ (a : A ⟶ SheafOfModules.unit R) {U V : Cᵒᵖ} (g : U ⟶ V)
    (z : A.val.obj U) :
    ringValue a V (A.val.restrictₛₗ g z) = R.obj.map g (ringValue a U z) :=
  PresheafOfModules.naturality_apply a.val g z

/-- Restricting twice is restricting along the composite. -/
lemma restrictₛₗ_restrictₛₗ (M : PresheafOfModules.{u} R.obj) {U V W : Cᵒᵖ} (h : U ⟶ V)
    (g : V ⟶ W) (z : M.obj U) :
    M.restrictₛₗ g (M.restrictₛₗ h z) = M.restrictₛₗ (h ≫ g) z :=
  (M.map_comp_apply h g z).symm

/-- The image product, written with `ringValue`. -/
lemma smul_ringValue_mem_imageProductSubmodule (a : A ⟶ SheafOfModules.unit R)
    (F : SheafOfModules.{u} R) (U : Cᵒᵖ) (z : A.val.obj U) (m : F.val.obj U) :
    ringValue a U z • m ∈ (imageProductSubmodule a F).obj U :=
  smul_mem_imageProductSubmodule a F U z m

/-- Restricting a product `a(z) • m` restricts both factors. -/
lemma restrictₛₗ_smul_ringValue (a : A ⟶ SheafOfModules.unit R) {U V : Cᵒᵖ} (g : U ⟶ V)
    (z : A.val.obj U) (m : F.val.obj U) :
    F.val.restrictₛₗ g (ringValue a U z • m) =
      ringValue a V (A.val.restrictₛₗ g z) • F.val.restrictₛₗ g m := by
  rw [(F.val.restrictₛₗ g).map_smulₛₗ, ringValue_restrictₛₗ]

/-! ### The sections of `A` multiplying `F` into a given submodule -/

/-- The sections of `A` which, read in `R` through `a`, multiply every section of `F` into `P`,
after every restriction. -/
private noncomputable def multiplierPresubmodule (a : A ⟶ SheafOfModules.unit R)
    (P : F.Submodule) : A.val.Submodule where
  obj U :=
    { carrier := {z : A.val.obj U | ∀ (V : Cᵒᵖ) (g : U ⟶ V) (m : F.val.obj V),
        ringValue a V (A.val.restrictₛₗ g z) • m ∈ P.obj V}
      zero_mem' := fun V g m => by
        rw [map_zero, ringValue_zero, zero_smul]
        exact zero_mem _
      add_mem' := fun {z z'} hz hz' V g m => by
        rw [map_add, ringValue_add, add_smul]
        exact add_mem (hz V g m) (hz' V g m)
      smul_mem' := fun r {z} hz V g m => by
        rw [(A.val.restrictₛₗ g).map_smulₛₗ, ringValue_smul, mul_smul]
        exact Submodule.smul_mem _ _ (hz V g m) }
  map := fun {U U'} h z hz V g m => by
    rw [restrictₛₗ_restrictₛₗ]
    exact hz V (h ≫ g) m

/-- A section of `A` multiplying `F` into `P` after every restriction multiplies it in on the
nose: membership in `P` is local, and the restrictions of a product are products. -/
private lemma smul_mem_of_forall_restrict (a : A ⟶ SheafOfModules.unit R) {P : F.Submodule}
    {U : Cᵒᵖ} {z : A.val.obj U}
    (hz : ∀ (V : Cᵒᵖ) (g : U ⟶ V) (m : F.val.obj V),
      ringValue a V (A.val.restrictₛₗ g z) • m ∈ P.obj V)
    (m : F.val.obj U) : ringValue a U z • m ∈ P.obj U := by
  refine P.isSheaf _ (J.superset_covering (fun W h _ => ?_) (J.top_mem U.unop))
  change F.val.restrictₛₗ h.op (ringValue a U z • m) ∈ P.obj (op W)
  rw [restrictₛₗ_smul_ringValue]
  exact hz (op W) h.op (F.val.restrictₛₗ h.op m)

/-- The sections of `A` which multiply `F` into `P` form a *sheaf* submodule: the membership
condition of `P` is local, and the condition here quantifies over all restrictions. -/
private noncomputable def multiplierSubmodule (a : A ⟶ SheafOfModules.unit R)
    (P : F.Submodule) : A.Submodule where
  toSubmodule := multiplierPresubmodule a P
  isSheaf := by
    intro U z hz V g m
    refine P.isSheaf _ (J.superset_covering ?_ (J.pullback_stable g.unop hz))
    intro W h hh
    have hmem : A.val.restrictₛₗ (g ≫ h.op) z ∈ (multiplierPresubmodule a P).obj (op W) := by
      rw [show (g ≫ h.op) = (h ≫ g.unop).op from by simp]
      exact hh
    change F.val.restrictₛₗ h.op (ringValue a V (A.val.restrictₛₗ g z) • m) ∈ P.obj (op W)
    rw [restrictₛₗ_smul_ringValue, restrictₛₗ_restrictₛₗ]
    exact smul_mem_of_forall_restrict a hmem (F.val.restrictₛₗ h.op m)

/-! ### The theorem -/

variable {R₁ : Sheaf J RingCat.{u}} {α : R₁ ⟶ R} {M : SheafOfModules.{u} R₁}

/-- The family of sections of `R` read off the sections of `M` through `u` and then `a`. -/
noncomputable def unitImageSections (u : M ⟶ (SheafOfModules.restrictScalars α).obj A)
    (a : A ⟶ SheafOfModules.unit R) (U : Cᵒᵖ) : Set (R.obj.obj U) :=
  Set.range fun j : M.val.obj U => ringValue a U (u.val.app U j)

/-- **The unit of an adjunction whose right adjoint is restriction of scalars cancels zero.**
This is the hypothesis `imageProductSubmodule_eq_unitImageSections` places on `u`, verified for
extension of scalars. -/
theorem restrictScalars_unit_cancel_zero
    {L : SheafOfModules.{u} R₁ ⥤ SheafOfModules.{u} R}
    (adj : L ⊣ SheafOfModules.restrictScalars.{u} α)
    [(SheafOfModules.restrictScalars.{u} α).Additive] (N : SheafOfModules.{u} R₁)
    (Z : SheafOfModules.{u} R) (g : L.obj N ⟶ Z)
    (hg : adj.unit.app N ≫ (SheafOfModules.restrictScalars.{u} α).map g = 0) : g = 0 := by
  refine (adj.homEquiv N Z).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  exact hg

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An extension of scalars multiplies out no more than its unit sections do.** The submodule
of `F` generated by the products of all sections of `A` is generated by the products of the
sections coming from `M`. -/
theorem imageProductSubmodule_eq_unitImageSections
    (u : M ⟶ (SheafOfModules.restrictScalars α).obj A)
    (hu : ∀ (Z : SheafOfModules.{u} R) (g : A ⟶ Z),
      u ≫ (SheafOfModules.restrictScalars α).map g = 0 → g = 0)
    (a : A ⟶ SheafOfModules.unit R) (F : SheafOfModules.{u} R) :
    imageProductSubmodule a F = sectionsProductSubmodule (unitImageSections u a) F := by
  refine le_antisymm ?_ (sectionsProductSubmodule_le fun U r hr m => ?_)
  · set P := sectionsProductSubmodule (unitImageSections u a) F with hP
    set S := multiplierSubmodule a P with hS
    have hgen : ∀ (U : Cᵒᵖ) (j : M.val.obj U),
        (u.val.app U j : A.val.obj U) ∈ S.obj U := by
      intro U j V g m
      rw [show A.val.restrictₛₗ g (u.val.app U j) = u.val.app V (M.val.restrictₛₗ g j) from
        (PresheafOfModules.naturality_apply u.val g j).symm]
      exact smul_mem_sectionsProductSubmodule (unitImageSections u a) F V
        (show _ ∈ unitImageSections u a V from ⟨M.val.restrictₛₗ g j, rfl⟩) m
    have hepi : Epi S.ι := by
      rw [Preadditive.epi_iff_cancel_zero]
      intro Z g hg
      have hkill : ∀ (W : Cᵒᵖ) (x : A.val.obj W), x ∈ S.obj W → g.val.app W x = 0 :=
        fun W x hx => congrArg (fun φ : S.toSheafOfModules ⟶ Z => φ.val.app W ⟨x, hx⟩) hg
      refine hu Z g (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
        ModuleCat.hom_ext (LinearMap.ext fun j => ?_)))
      exact hkill W (u.val.app W j) (hgen W j)
    have hall : ∀ (U : Cᵒᵖ) (z : A.val.obj U), z ∈ S.obj U := by
      intro U z
      refine S.isSheaf z (J.superset_covering ?_ (EpiMono.imageSieve_mem_of_epi S.ι z))
      rintro W h ⟨t, ht⟩
      have h2 : Subtype.val t = A.val.restrictₛₗ h.op z := ht
      change A.val.restrictₛₗ h.op z ∈ S.obj (op W)
      rw [← h2]
      exact t.2
    exact imageProductSubmodule_le a fun U z m =>
      smul_mem_of_forall_restrict a (hall U z) m
  · obtain ⟨j, rfl⟩ := hr
    exact smul_ringValue_mem_imageProductSubmodule a F U (u.val.app U j) m

end Stacks.SheafOfModules

end
