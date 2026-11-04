module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Limits of topological rings (Stacks 0B23)

Throughout, following the Stacks Project convention, "ring" means a commutative ring with
`1`, so the category of topological rings is Mathlib's `TopCommRingCat`, whose objects carry
a `CommRing`, a `TopologicalSpace` and an `IsTopologicalRing` instance, and whose morphisms
are the continuous ring homomorphisms. The tag says that this category has all small limits
and that the two forgetful functors — to `TopCat` and to `CommRingCat` — preserve them.

All three statements come from one construction, given here once as
`TopCommRingCat.limitCone` and `TopCommRingCat.limitConeIsLimit`: for `F : J ⥤ TopCommRingCat`
the limit is the subring
`{(xⱼ) ∈ ∏ⱼ F(j) | F(f)(xⱼ) = x_k for every f : j ⟶ k}`
of the product, with the subspace topology of the product topology (a topological ring
automatically), and with the restricted product projections as the cone maps. Preservation by
each forgetful functor is then `preservesLimit_of_preserves_limit_cone` applied to that one
cone: its image under `forget₂ … TopCat` is literally `TopCat.limitCone`, and its image under
`forget₂ … CommRingCat` is checked to be a limit directly.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopCommRingCat

variable {J : Type u} [SmallCategory J]

/-- The subring of *sections* of a diagram of topological rings: those families `(xⱼ)` in the
product of the underlying rings that are compatible with every arrow of the diagram. -/
def limitSubring (F : J ⥤ TopCommRingCat.{u}) : Subring ((j : J) → (F.obj j).α) where
  carrier := { x | ∀ ⦃j k : J⦄ (f : j ⟶ k), (F.map f).1 (x j) = x k }
  mul_mem' := by intro a b ha hb j k f; simp [Pi.mul_apply, map_mul, ha f, hb f]
  one_mem' := by intro j k f; simp [map_one]
  add_mem' := by intro a b ha hb j k f; simp [Pi.add_apply, map_add, ha f, hb f]
  zero_mem' := by intro j k f; simp [map_zero]
  neg_mem' := by intro a ha j k f; simp [Pi.neg_apply, map_neg, ha f]

/-- The cone on `F` whose apex is `TopCommRingCat.limitSubring F` carrying the subspace
topology, with the restricted product projections as its legs. -/
def limitCone (F : J ⥤ TopCommRingCat.{u}) : Cone F where
  pt := TopCommRingCat.of (limitSubring F)
  π :=
    { app := fun j =>
        ⟨(Pi.evalRingHom (fun j => (F.obj j).α) j).comp (limitSubring F).subtype,
         (continuous_apply j).comp continuous_subtype_val⟩
      naturality := by
        intro j k f
        simp only [Functor.const_obj_map]
        ext ⟨x, hx⟩
        simp only [Functor.const_obj_obj, limitSubring]
        exact (hx f).symm }

/-- `TopCommRingCat.limitCone` is a limit cone: a cone `s` factors through it by the family of
its own legs, which is a section by naturality, is a ring homomorphism componentwise, and is
continuous into the subspace topology because each leg is. -/
def limitConeIsLimit (F : J ⥤ TopCommRingCat.{u}) : IsLimit (limitCone F) where
  lift s :=
    ⟨{ toFun := fun x => ⟨fun j => (s.π.app j).1 x, fun j k f => by
          have h' : s.π.app j ≫ F.map f = s.π.app k := by
            have h := s.π.naturality f; rw [← h]; simp
          exact congr_arg (fun g => g.1 x) h'⟩
       map_one' := by apply Subtype.ext; funext j; exact map_one (s.π.app j).1
       map_mul' := fun a b => by apply Subtype.ext; funext j; exact map_mul (s.π.app j).1 a b
       map_zero' := by apply Subtype.ext; funext j; exact map_zero (s.π.app j).1
       map_add' := fun a b => by apply Subtype.ext; funext j; exact map_add (s.π.app j).1 a b },
     by apply continuous_induced_rng.mpr; apply continuous_pi; intro j; exact (s.π.app j).2⟩
  fac := by intro s j; ext x; rfl
  uniq := by
    intro s m hm
    ext x
    apply Subtype.ext
    funext j
    exact congr_arg (fun g => g.1 x) (hm j)

/-- **Stacks 0B23.** The category of topological rings has all small limits. -/
@[stacks 0B23 "existence of limits"]
instance hasLimits : HasLimits TopCommRingCat.{u} := by
  constructor
  intro J _
  constructor
  intro F
  exact HasLimit.mk ⟨limitCone F, limitConeIsLimit F⟩

/-- **Stacks 0B23**, part (a). The forgetful functor to topological spaces preserves all
small limits: it carries `TopCommRingCat.limitCone` to `TopCat.limitCone`. -/
@[stacks 0B23 "part (a): commutes with forgetful to TopCat"]
instance preservesLimits_forget₂TopCat :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) := by
  constructor
  intro J _
  constructor
  intro F
  apply preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
  exact TopCat.limitConeIsLimit (F ⋙ forget₂ TopCommRingCat TopCat)

/-- **Stacks 0B23**, part (b). The forgetful functor to rings preserves all small limits:
the image of `TopCommRingCat.limitCone` is the subring of sections of the underlying diagram
of rings, which is a limit there for the same reason. -/
@[stacks 0B23 "part (b): commutes with forgetful to CommRing"]
instance preservesLimits_forget₂CommRingCat :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  constructor
  intro J _
  constructor
  intro F
  apply preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
  refine IsLimit.mk (fun s => ?_) ?_ ?_
  · refine CommRingCat.ofHom ?_
    refine { toFun := fun x => ⟨fun j => (s.π.app j).hom x, fun j k f => ?_⟩
             map_one' := ?_
             map_mul' := ?_
             map_zero' := ?_
             map_add' := ?_ }
    · have h2 : (s.π.app j ≫ (F ⋙ forget₂ TopCommRingCat CommRingCat).map f) = s.π.app k := by
        rw [← s.π.naturality f]; simp
      exact congr_arg (fun g => g.hom x) h2
    · apply Subtype.ext; funext j; exact map_one (s.π.app j).hom
    · intro a b; apply Subtype.ext; funext j; exact map_mul (s.π.app j).hom a b
    · apply Subtype.ext; funext j; exact map_zero (s.π.app j).hom
    · intro a b; apply Subtype.ext; funext j; exact map_add (s.π.app j).hom a b
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    apply Subtype.ext
    funext j
    exact congr_arg (fun g => g.hom x) (hm j)

end TopCommRingCat
