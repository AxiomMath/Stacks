module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent

/-!
# An isomorphism of modules under `𝒪` between quotient algebras is an isomorphism of algebras

Let `A` and `C` be sheaves of `𝒪_F`-algebras on an algebraic space `F` whose structure maps
`𝒪_F ⟶ A` are locally surjective, as for the direct image of the structure sheaf along a closed
immersion. Then every isomorphism of the underlying `𝒪_F`-modules carrying the unit of `A` to
the unit of `C` is multiplicative, hence an isomorphism of algebra sheaves.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.map_mul_of_isLocallySurjective`: such a module map is
  multiplicative.
* `AlgebraicGeometry.Space.AlgebraSheaf.isoOfUnderlyingModuleIso`: the resulting isomorphism of
  algebra sheaves.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {A C : AlgebraSheaf.{u, u} B S hS F hF}

/-- The value on sections of a morphism of the underlying modules of two algebra sheaves, read
as a map of the sections of the sheaves of rings. -/
abbrev sectionMap (e : A.underlyingModule ⟶ C.underlyingModule) (U : (SmallEtale B S hS F)ᵒᵖ)
    (x : A.right.obj.obj U) : C.right.obj.obj U :=
  e.val.app U x

/-- A morphism of underlying modules commutes with the restriction of sections. -/
theorem sectionMap_map (e : A.underlyingModule ⟶ C.underlyingModule)
    {U V : (SmallEtale B S hS F)ᵒᵖ} (f : U ⟶ V) (x : A.right.obj.obj U) :
    sectionMap e V (A.right.obj.map f x) = C.right.obj.map f (sectionMap e U x) :=
  PresheafOfModules.naturality_apply e.val f x

/-- A morphism of underlying modules is additive on sections. -/
theorem sectionMap_add (e : A.underlyingModule ⟶ C.underlyingModule)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x y : A.right.obj.obj U) :
    sectionMap e U (x + y) = sectionMap e U x + sectionMap e U y :=
  map_add (e.val.app U).hom x y

/-- A morphism of underlying modules is linear over the functions on sections: it commutes with
multiplication by the image of a function. -/
theorem sectionMap_algebraMap_mul (e : A.underlyingModule ⟶ C.underlyingModule)
    (U : (SmallEtale B S hS F)ᵒᵖ) (r : (structureSheaf B S hS F hF).obj.obj U)
    (x : A.right.obj.obj U) :
    sectionMap e U (A.algebraMap U r * x) = C.algebraMap U r * sectionMap e U x :=
  LinearMap.map_smul (e.val.app U).hom r x

/-- **A morphism of underlying modules carrying the unit to the unit is multiplicative**, when the
structure map of the source is locally surjective. -/
theorem map_mul_of_isLocallySurjective (e : A.underlyingModule ⟶ C.underlyingModule)
    (hu : ∀ U r, sectionMap e U (A.algebraMap U r) = C.algebraMap U r)
    (hloc : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) A.hom.hom)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x y : A.right.obj.obj U) :
    sectionMap e U (x * y) = sectionMap e U x * sectionMap e U y := by
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (C.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ C.right.property)
  refine (hsheaf _ (hloc.imageSieve_mem x)).isSeparatedFor.ext fun V f hf => ?_
  obtain ⟨r, hr⟩ := hf
  have hr' : A.algebraMap (op V) r = A.right.obj.map f.op x := hr
  change C.right.obj.map f.op (sectionMap e U (x * y)) =
    C.right.obj.map f.op (sectionMap e U x * sectionMap e U y)
  rw [map_mul, ← sectionMap_map, ← sectionMap_map, ← sectionMap_map, map_mul, ← hr',
    sectionMap_algebraMap_mul, hu]

/-- The morphism of sheaves of rings underlying a multiplicative unital morphism of the underlying
modules of two algebra sheaves. -/
def ringSheafHomOfUnderlyingModuleHom (e : A.underlyingModule ⟶ C.underlyingModule)
    (hu : ∀ U r, sectionMap e U (A.algebraMap U r) = C.algebraMap U r)
    (hloc : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) A.hom.hom) :
    A ⟶ C where
  right :=
    { hom :=
        { app := fun U => CommRingCat.ofHom
            { toFun := sectionMap e U
              map_one' := by
                rw [← map_one (A.algebraMap U), hu, map_one]
              map_mul' := map_mul_of_isLocallySurjective e hu hloc U
              map_zero' := map_zero (e.val.app U).hom
              map_add' := sectionMap_add e U }
          naturality := fun U V f => by
            ext x
            exact sectionMap_map e f x } }
  comm U r := hu U r

/-- **An isomorphism of modules under `𝒪` between algebra sheaves with locally surjective structure
maps is an isomorphism of algebra sheaves.** -/
def isoOfUnderlyingModuleIso (e : A.underlyingModule ≅ C.underlyingModule)
    (hu : ∀ U r, sectionMap e.hom U (A.algebraMap U r) = C.algebraMap U r)
    (hA : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) A.hom.hom)
    (hC : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) C.hom.hom) : A ≅ C where
  hom := ringSheafHomOfUnderlyingModuleHom e.hom hu hA
  inv := ringSheafHomOfUnderlyingModuleHom e.inv (fun U r => by
      rw [← hu]
      exact congrArg (fun g : A.underlyingModule ⟶ A.underlyingModule => g.val.app U _)
        e.hom_inv_id) hC
  hom_inv_id := by
    refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
    ext x
    exact congrArg (fun g : A.underlyingModule ⟶ A.underlyingModule => g.val.app U x) e.hom_inv_id
  inv_hom_id := by
    refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
    ext x
    exact congrArg (fun g : C.underlyingModule ⟶ C.underlyingModule => g.val.app U x) e.inv_hom_id

/-- The algebra isomorphism of `AlgebraicGeometry.Space.AlgebraSheaf.isoOfUnderlyingModuleIso` has
the given module isomorphism as its underlying map of sections. -/
theorem isoOfUnderlyingModuleIso_hom_right_app (e : A.underlyingModule ≅ C.underlyingModule)
    (hu : ∀ U r, sectionMap e.hom U (A.algebraMap U r) = C.algebraMap U r)
    (hA : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) A.hom.hom)
    (hC : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) C.hom.hom)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : A.right.obj.obj U) :
    (isoOfUnderlyingModuleIso e hu hA hC).hom.right.hom.app U x = sectionMap e.hom U x :=
  rfl

end AlgebraSheaf

end AlgebraicGeometry.Space

end
