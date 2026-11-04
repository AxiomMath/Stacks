module

public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# Identifying a sheaf of modules with the sheafification of a presheaf known on a basis

Let `X` be a topological space, `𝒪` a sheaf of rings on `X`, `P` a presheaf of `𝒪`-modules and
`η : P ⟶ M` a morphism into a *sheaf* of `𝒪`-modules which is locally bijective — the case to
have in mind is the unit of sheafification, so that `M` is the sheafification of `P`. Let `G` be
another sheaf of `𝒪`-modules and suppose given, over the members of a basis of the topology,
isomorphisms

`e_V : Γ(V, G) ≅ P(V)`

compatible with the restriction maps. Then `G ≅ M`.

## Why this is not another basis criterion

The repository already has criteria for *inverting a given morphism* from its behaviour on a
basis — `Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis` for a
morphism of sheaves and
`Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_sheafification_map_of_bijective_basis`
for a morphism of presheaves — and `Stacks.BasisRestriction.moduleSheafIsoOfSectionIsoOnBasis`
for assembling an isomorphism of *sheaves* out of isomorphisms on a basis. None of them applies
here, and the reason is the direction of the available data.

The family `e_V` compares the sections of a sheaf with the sections of a *presheaf*. Gluing it
into a morphism `G ⟶ M` is possible — `e_V` followed by `η` is a family of maps between the
sections of two sheaves, which `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`
assembles. But that glued morphism is **not** invertible on the basis: its component over `V` is
`e_V` followed by `η_V`, and `η_V` is only locally bijective, not bijective. So neither
`isIso_of_isIso_val_app_basis` nor `isIso_sheafification_map_of_bijective_basis` can be applied
to it. Nor can the family be glued in the opposite direction: a morphism of presheaves out of a
sheaf is not determined by data on a basis.

What *is* true is that the glued morphism is **locally** bijective, because local bijectivity
only has to be witnessed on a neighbourhood of each point and every point has a basis
neighbourhood inside any given one. That is the content below, and
`Stacks.SheafOfModules.isIso_of_isLocallyBijective` then inverts it.

## Main results

* `Stacks.BasisRestriction.basisSectionsHom` — the morphism `G ⟶ M` glued from the family
  followed by `η`, and `Stacks.BasisRestriction.basisSectionsHom_app`, its components over the
  members of the basis.
* `Stacks.BasisRestriction.isLocallyInjective_basisSectionsHom` and
  `Stacks.BasisRestriction.isLocallySurjective_basisSectionsHom` — it is locally injective and
  locally surjective.
* `Stacks.BasisRestriction.isIso_basisSectionsHom` — hence an isomorphism, and
  `Stacks.BasisRestriction.moduleSheafIsoOfBasisSectionsIso`, the resulting isomorphism
  `G ≅ M`.

## References

* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.BasisRestriction

universe u

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat.{u} X}

section LocallyBijective

variable (G M : SheafOfModules.{u} 𝒪) (P : PresheafOfModules.{u} 𝒪.obj) (η : P ⟶ M.val)
  {ι : Type*} (U : ι → Opens X)
  (e : ∀ a, G.val.obj (op (U a)) ⟶ P.obj (op (U a)))

/-- The compatibility with restriction of a family of maps from the sections of a sheaf of
modules to the sections of a presheaf of modules, over the members of a basis. This is the
`Stacks.BasisRestriction.IsCompatibleOnBasis` of `ModuleHomOnBasis.lean` with the target allowed
to be a presheaf. -/
def IsCompatibleOnBasisPresheaf : Prop :=
  ∀ a b (h : U b ≤ U a) (s : G.val.obj (op (U a))),
    e b (G.val.map (homOfLE h).op s) = P.map (homOfLE h).op (e a s)

/-- Following the family by `η` gives a family of maps between the sections of two *sheaves*,
and it is compatible with restriction because `η` is a morphism of presheaves. -/
theorem isCompatibleOnBasis_comp (hcomp : IsCompatibleOnBasisPresheaf G P U e) :
    IsCompatibleOnBasis G M U (fun a => e a ≫ η.app (op (U a))) := by
  intro a b h s
  have h₁ : (e b ≫ η.app (op (U b))) (G.val.map (homOfLE h).op s) =
      η.app (op (U b)) (e b (G.val.map (homOfLE h).op s)) :=
    ConcreteCategory.comp_apply _ _ _
  have h₂ : (e a ≫ η.app (op (U a))) s = η.app (op (U a)) (e a s) :=
    ConcreteCategory.comp_apply _ _ _
  rw [h₁, h₂, hcomp a b h s]
  exact PresheafOfModules.naturality_apply η (homOfLE h).op (e a s)

/-- The morphism of sheaves of modules glued from the family followed by `η`. -/
noncomputable def basisSectionsHom (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e) : G ⟶ M :=
  moduleSheafHomOfSectionHomOnBasis G M U (fun a => e a ≫ η.app (op (U a))) hU
    (isCompatibleOnBasis_comp G M P η U e hcomp)

/-- Over a member of the basis, the glued morphism is the given map followed by `η`. -/
theorem basisSectionsHom_app (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e) (a : ι)
    (s : G.val.obj (op (U a))) :
    (basisSectionsHom G M P η U e hU hcomp).val.app (op (U a)) s =
      η.app (op (U a)) (e a s) :=
  (congrArg (fun f : G.val.obj (op (U a)) ⟶ M.val.obj (op (U a)) => f s)
    (moduleSheafHomOfSectionHomOnBasis_app G M U
      (fun a => e a ≫ η.app (op (U a))) hU
      (isCompatibleOnBasis_comp G M P η U e hcomp) a)).trans
    (ConcreteCategory.comp_apply _ _ _)

/-- Restricting twice is restricting once: the arrows of `Opens X` between two given opens are
unique, so the composite of two restrictions is the restriction along the only arrow available. -/
theorem map_restrict_restrict (Q : PresheafOfModules.{u} 𝒪.obj) {A B C : Opens X}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (s : Q.obj (op C)) :
    Q.map f.op (Q.map g.op s) = Q.map h.op s :=
  (PresheafOfModules.map_comp_apply Q g.op f.op s).symm.trans
    (PresheafOfModules.congr_map_apply Q (Subsingleton.elim _ _) s)

/-- **The glued morphism is locally injective.** Over a basis member its component is `e a`
followed by `η`; two sections with the same image therefore have the same image under `η` after
restriction to a basis member, and `η` is locally injective, so they agree on a neighbourhood of
each point — which can be shrunk to a basis member, where `e` is injective. -/
theorem isLocallyInjective_basisSectionsHom (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e)
    (hinj : ∀ a, Function.Injective (e a))
    (hηi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map
        (basisSectionsHom G M P η U e hU hcomp).val) := by
  constructor
  intro W x y hxy p hp
  obtain ⟨V, ⟨a, rfl⟩, hpV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hU hp
  have hxy' : (basisSectionsHom G M P η U e hU hcomp).val.app W x =
      (basisSectionsHom G M P η U e hU hcomp).val.app W y := hxy
  have hres : ∀ z : G.val.obj W,
      η.app (op (U a)) (e a (G.val.map (homOfLE hVW).op z)) =
        M.val.map (homOfLE hVW).op
          ((basisSectionsHom G M P η U e hU hcomp).val.app W z) := fun z =>
    (basisSectionsHom_app G M P η U e hU hcomp a _).symm.trans
      (PresheafOfModules.naturality_apply
        (basisSectionsHom G M P η U e hU hcomp).val (homOfLE hVW).op z)
  have key : η.app (op (U a)) (e a (G.val.map (homOfLE hVW).op x)) =
      η.app (op (U a)) (e a (G.val.map (homOfLE hVW).op y)) :=
    ((hres x).trans (congrArg (M.val.map (homOfLE hVW).op) hxy')).trans (hres y).symm
  obtain ⟨V', f, hf, hpV'⟩ :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η) _ _ key p hpV
  obtain ⟨V'', ⟨b, rfl⟩, hpV'', hV''V'⟩ := Opens.isBasis_iff_nbhd.mp hU hpV'
  have hf' : P.map f.op (e a (G.val.map (homOfLE hVW).op x)) =
      P.map f.op (e a (G.val.map (homOfLE hVW).op y)) := hf
  have hba : U b ≤ U a := hV''V'.trans (leOfHom f)
  have hstep : ∀ z : G.val.obj W,
      e b (G.val.map (homOfLE (hba.trans hVW)).op z) =
        P.map (homOfLE hba).op (e a (G.val.map (homOfLE hVW).op z)) := fun z =>
    (congrArg (e b) (map_restrict_restrict G.val (homOfLE hba) (homOfLE hVW)
      (homOfLE (hba.trans hVW)) z)).symm.trans (hcomp a b hba _)
  refine ⟨U b, homOfLE (hba.trans hVW), ?_, hpV''⟩
  have final : G.val.map (homOfLE (hba.trans hVW)).op x =
      G.val.map (homOfLE (hba.trans hVW)).op y :=
    hinj b <| (hstep x).trans
      (((map_restrict_restrict P (homOfLE hV''V') f (homOfLE hba) _).symm.trans
        ((congrArg (P.map (homOfLE hV''V').op) hf').trans
          (map_restrict_restrict P (homOfLE hV''V') f (homOfLE hba) _))).trans (hstep y).symm)
  exact final

/-- **The glued morphism is locally surjective.** A section of `M` is locally in the image of
`η`, and every point has a basis neighbourhood inside the open where it is; there `e` is
surjective, so the lift through `η` comes from a section of `G`. -/
theorem isLocallySurjective_basisSectionsHom (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e)
    (hsurj : ∀ a, Function.Surjective (e a))
    (hηs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map
        (basisSectionsHom G M P η U e hU hcomp).val) := by
  constructor
  intro W t p hp
  obtain ⟨V, ⟨a, rfl⟩, hpV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hU hp
  obtain ⟨V', f, ⟨z, hz⟩, hpV'⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η)
      (M.val.map (homOfLE hVW).op t) p hpV
  obtain ⟨V'', ⟨b, rfl⟩, hpV'', hV''V'⟩ := Opens.isBasis_iff_nbhd.mp hU hpV'
  have hba : U b ≤ U a := hV''V'.trans (leOfHom f)
  obtain ⟨w, hw⟩ := hsurj b (P.map (homOfLE hV''V').op z)
  have hz' : η.app (op V') z = M.val.map f.op (M.val.map (homOfLE hVW).op t) := hz
  refine ⟨U b, homOfLE (hba.trans hVW), ⟨w, ?_⟩, hpV''⟩
  have final : (basisSectionsHom G M P η U e hU hcomp).val.app (op (U b)) w =
      M.val.map (homOfLE (hba.trans hVW)).op t :=
    (basisSectionsHom_app G M P η U e hU hcomp b w).trans
      ((congrArg (η.app (op (U b))) hw).trans
        ((PresheafOfModules.naturality_apply η (homOfLE hV''V').op z).trans
          ((congrArg (M.val.map (homOfLE hV''V').op) hz').trans
            ((map_restrict_restrict M.val (homOfLE hV''V') f (homOfLE hba) _).trans
              (map_restrict_restrict M.val (homOfLE hba) (homOfLE hVW)
                (homOfLE (hba.trans hVW)) t)))))
  exact final

/-- **The glued morphism is an isomorphism**, by
`Stacks.SheafOfModules.isIso_of_isLocallyBijective`. -/
theorem isIso_basisSectionsHom (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e)
    (hbij : ∀ a, Function.Bijective (e a))
    (hηi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η))
    (hηs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η)) :
    IsIso (basisSectionsHom G M P η U e hU hcomp) := by
  have := isLocallyInjective_basisSectionsHom G M P η U e hU hcomp (fun a => (hbij a).1) hηi
  have := isLocallySurjective_basisSectionsHom G M P η U e hU hcomp (fun a => (hbij a).2) hηs
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective _

/-- **A sheaf of modules whose sections over a basis are the sections there of a presheaf is the
target of any locally bijective morphism out of that presheaf.** With `η : P ⟶ M` locally
bijective into a sheaf `M` and bijections `e_V : Γ(V, G) ⟶ P(V)` over a basis, compatible with
restriction, `G ≅ M`; the isomorphism is `e` followed by `η`, glued. -/
noncomputable def moduleSheafIsoOfBasisSectionsIso (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasisPresheaf G P U e)
    (hbij : ∀ a, Function.Bijective (e a))
    (hηi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η))
    (hηs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf 𝒪.obj).map η)) :
    G ≅ M :=
  haveI := isIso_basisSectionsHom G M P η U e hU hcomp hbij hηi hηs
  asIso (basisSectionsHom G M P η U e hU hcomp)

end LocallyBijective

end Stacks.BasisRestriction

end
