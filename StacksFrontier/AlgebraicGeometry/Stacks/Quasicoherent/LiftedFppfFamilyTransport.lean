module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilySheafCondition

/-!
# The quasi-coherent module below an object, and the transport downstairs (Stacks 076T)

Let `F` be a presheaf of modules over the structure sheaf of a category `𝒳` fibred in groupoids
over the big fppf site of `S`, and let `x` be an object of `𝒳` lying over a scheme `U`. A
quasi-coherent module below `x` is a quasi-coherent `𝒪_U`-module `𝓕` with `𝓕^a ≅ F|_{U_ét}`; one
exists when `F` is locally quasi-coherent. Through it, the sections of the presheaf
`AlgebraicGeometry.Stack.overPostTransportSections` on the big fppf site of `U` are identified with
those of the presheaf `𝒢^a` formed from `𝓕`, and the sheaf condition for `𝒢^a` (Descent,
**Stacks 03DT**) is transported to `AlgebraicGeometry.Stack.overPostTransportSections` along a
family of the big fppf site of `U` lying over an fppf covering, under hypothesis (b) of
**Stacks 076T**.

## Main definitions

* `AlgebraicGeometry.Stack.QuasicoherentBelow`: the quasi-coherent module below an object of `𝒳`.
* `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMap`: the identification of
  `AlgebraicGeometry.Stack.overPostSectionsMap` read at it.

## Main results

* `AlgebraicGeometry.Stack.nonempty_quasicoherentBelow`: a locally quasi-coherent presheaf of
  modules has a quasi-coherent module below every object.
* `AlgebraicGeometry.Stack.QuasicoherentBelow.isSheafFor_sectionsTypes`: Descent, Stacks 03DT, at
  it.
* `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMap_bijective`,
  `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMap_naturality`: the identification is a
  bijection, and over the carried cocycle it commutes with the restriction maps of the big fppf
  site of `U`.
* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_overPostLift`: hypothesis (b)
  of Stacks 076T, read at one object of the big fppf site of `U`.
* `AlgebraicGeometry.Stack.isSheafFor_overPostTransportSections_of_isIso` and
  `AlgebraicGeometry.Stack.isSheafFor_overPostTransportSections`: the sheaf condition for
  `AlgebraicGeometry.Stack.overPostTransportSections`, first given the isomorphisms of the
  comparison maps at the objects involved, then given hypothesis (b) of Stacks 076T.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-! ### The quasi-coherent module below an object -/

/-- The quasi-coherent module below an object of `𝒳`: for a presheaf of modules `F` over the
structure sheaf of **Stacks 06TV** and an object `x` of `𝒳` lying over a scheme `U`, a
quasi-coherent `𝒪_U`-module `𝓕` together with an identification of the module `𝓕^a` it
determines on the small étale site of `U` with the restriction `F|_{U_ét}` of **Stacks 06WJ**,
which is a sheaf. -/
structure QuasicoherentBelow (x : 𝒳) where
  /-- The quasi-coherent module on the scheme below `x`. -/
  val : (p.obj x).left.1.Modules
  /-- The module is quasi-coherent. -/
  isQuasicoherent : val.IsQuasicoherent
  /-- The restriction of `F` to the small étale site of the scheme below `x` is a sheaf. -/
  isSheaf : Presheaf.IsSheaf
    (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
    (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf
  /-- The associated module of `val` on the small étale site is the restriction of `F`. -/
  iso : (SmallEtale.associatedModule E (p.obj x).left.1 (contains_base B E h S hS p x)).obj val ≅
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F, isSheaf⟩

/-- A locally quasi-coherent presheaf of modules has a quasi-coherent module below every object
of `𝒳`. -/
theorem nonempty_quasicoherentBelow (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) (x : 𝒳) :
    Nonempty (QuasicoherentBelow B E h S hS p hp F x) := by
  obtain ⟨𝓕, h𝓕, -, hMx, ⟨eU⟩⟩ :=
    exists_isSheaf_sectionsPresheafOfModules_of_isLocallyQuasicoherent B E h S hS p hp F hlqc x
  exact ⟨⟨𝓕, h𝓕, hMx, eU⟩⟩

namespace QuasicoherentBelow

variable {B E h S hS p hp F} {x : 𝒳} (d : QuasicoherentBelow B E h S hS p hp F x)

/-- Descent, **Stacks 03DT**, at the quasi-coherent module below `x`: the presheaf `𝒢^a` it
determines is a sheaf for the fppf topology of the big fppf site of the scheme below `x`. -/
theorem isSheaf_sectionsPresheaf :
    Presheaf.IsSheaf (BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf)
      (overPostSectionsPresheaf B S hS p x d.val d.isQuasicoherent) :=
  have := d.isQuasicoherent
  BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology B (p.obj x).left.1
    (p.obj x).left.2 .fppf d.val

/-- The sheaf condition for `𝒢^a` along a family of the big fppf site of `U` generating a
covering sieve. -/
theorem isSheafFor_sectionsTypes {I : Type t}
    (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
    (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
      BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
        (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M)
      (Presieve.ofArrows X π) :=
  (Presieve.isSheafFor_iff_generate _).2 (d.isSheaf_sectionsPresheaf M _ hcov)

/-- The identification of the sections of `AlgebraicGeometry.Stack.overPostSectionsMap` at the
quasi-coherent module below `x`. -/
noncomputable def sectionsMap (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).obj (op V) :=
  overPostSectionsMap B E h S hS p hp F hlqc x V d.val d.isQuasicoherent d.isSheaf d.iso hiso M

/-- `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMap` is a bijection. -/
theorem sectionsMap_bijective (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (d.sectionsMap hlqc V hiso M) :=
  overPostSectionsMap_bijective B E h S hS p hp F hlqc x V d.val d.isQuasicoherent d.isSheaf
    d.iso hiso M

/-- Over the carried cocycle, `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMap` commutes
with the restriction maps of the big fppf site of `U`. -/
theorem sectionsMap_naturality (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hcoc : LiftedSectionsCocycle B E h S hS p hp)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V) (etaleTopology B) (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp x V') (etaleTopology B) (etaleTopology_le_topology B) F))
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    d.sectionsMap hlqc V' hiso' M ((overPostTransportSections B S hS p hp F x M).map r.op s) =
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).map r.op
        (d.sectionsMap hlqc V hiso M s) :=
  overPostSectionsMap_naturality B E h S hS p hp F hlqc hcoc x r d.val d.isQuasicoherent
    d.isSheaf d.iso hiso hiso' M s

end QuasicoherentBelow

/-! ### Hypothesis (b) consumed at one object of the big fppf site of `U` -/

/-- Hypothesis (b) of Stacks 076T at one object of the big fppf site of `U`: the comparison
map `c_φ` of **Stacks 06WC** is an isomorphism along the arrow of `𝒳` which the localization
equivalence of **Stacks 06W0** produces over an object of the big fppf site of the scheme below
`x` lying over a flat morphism locally of finite presentation. -/
theorem isIso_restrictModulePullbackComparison_overPostLift
    (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F)
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hflat : Flat (B.inclusion.map V.hom))
    (hlfp : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp (overPostLiftHom B S hS p hp x V)
      (etaleTopology B) (etaleTopology_le_topology B) F) :=
  hbc _ (flat_overPostLift B S hS p hp x V hflat)
    (locallyOfFinitePresentation_overPostLift B S hS p hp x V hlfp)

section Transport

attribute [local irreducible] overPostTransportSections overPostSectionsTypes
  QuasicoherentBelow.sectionsMap

/-! ### The transport, downstairs on the big fppf site of `U` -/

section OfIsIso

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hcoc : LiftedSectionsCocycle B E h S hS p hp) {x : 𝒳}
  (d : QuasicoherentBelow B E h S hS p hp F x)
  {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
  (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
  {W : I → I → Over ((p ⋙ Over.forget (B.obj hS)).obj x)}
  (pr₁ : ∀ i j, W i j ⟶ X i) (pr₂ : ∀ i j, W i j ⟶ X j)
  (hW : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (π i) (π j))
  (hisoY : IsIso (restrictModulePullbackComparison B E h S hS p hp
    (overPostLiftHom B S hS p hp x (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (etaleTopology B) (etaleTopology_le_topology B) F))
  (hisoX : ∀ i, IsIso (restrictModulePullbackComparison B E h S hS p hp
    (overPostLiftHom B S hS p hp x (X i)) (etaleTopology B)
    (etaleTopology_le_topology B) F))
  (hisoW : ∀ i j, IsIso (restrictModulePullbackComparison B E h S hS p hp
    (overPostLiftHom B S hS p hp x (W i j)) (etaleTopology B)
    (etaleTopology_le_topology B) F))
  (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
    BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
      (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
  (M : AddCommGrpCat.{u})

include hlqc hcoc d hW hisoY hisoX hisoW hcov M in
/-- Let `{π i : U_i / U → U / U}` be a family of arrows of the big fppf site of the scheme `U`
below `x` which generates a covering sieve, with prescribed fibre products `W i j`, and suppose the
comparison map `c_φ` of **Stacks 06WC** is an isomorphism along the arrows of `𝒳` which the
localization equivalence of **Stacks 06W0** produces over `U / U`, over each `U_i / U` and over
each `W i j`. Then the transported presheaf
`AlgebraicGeometry.Stack.overPostTransportSections` satisfies the sheaf condition for the
family. -/
theorem isSheafFor_overPostTransportSections_of_isIso :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp F x M)
      (Presieve.ofArrows X π) :=
  Presieve.Arrows.isSheafFor_ofArrows_of_maps
    (Q := overPostTransportSections B S hS p hp F x M)
    (Q' := overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M)
    (Y := Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) (X := X) (W := W)
    π pr₁ pr₂ hW
    (d.sectionsMap hlqc (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) hisoY M)
    (d.sectionsMap_bijective hlqc (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) hisoY M)
    (fun i ↦ d.sectionsMap hlqc (X i) (hisoX i) M)
    (fun i ↦ (d.sectionsMap_bijective hlqc (X i) (hisoX i) M).injective)
    (fun i j ↦ d.sectionsMap hlqc (W i j) (hisoW i j) M)
    (fun i s ↦ d.sectionsMap_naturality hlqc hcoc (π i) hisoY (hisoX i) M s)
    (fun i j s ↦ d.sectionsMap_naturality hlqc hcoc (pr₁ i j) (hisoX i) (hisoW i j) M s)
    (fun i j s ↦ d.sectionsMap_naturality hlqc hcoc (pr₂ i j) (hisoX j) (hisoW i j) M s)
    (d.isSheafFor_sectionsTypes X π hcov M)

end OfIsIso

section OfFlat

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)
  (hcoc : LiftedSectionsCocycle B E h S hS p hp) {x : 𝒳}
  (d : QuasicoherentBelow B E h S hS p hp F x)
  {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
  (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
  (hflat : ∀ i, Flat (B.inclusion.map (X i).hom))
  (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (X i).hom))
  (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
    BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
      (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
  (M : AddCommGrpCat.{u})

include hlqc hbc hcoc d hflat hlfp hcov M in
/-- Under hypothesis (b) of **Stacks 076T**, the transported presheaf
`AlgebraicGeometry.Stack.overPostTransportSections` satisfies the sheaf condition for a family of
the big fppf site of `U` which generates a covering sieve and whose members lie over flat
morphisms locally of finite presentation. -/
theorem isSheafFor_overPostTransportSections :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp F x M)
      (Presieve.ofArrows X π) := by
  have hleft : ∀ i, (π i).left = (X i).hom := fun i ↦ by simpa using Over.w (π i)
  exact isSheafFor_overPostTransportSections_of_isIso B E h S hS p hp F hlqc hcoc d X π
    (fun i j ↦ pullback.fst (π i) (π j)) (fun i j ↦ pullback.snd (π i) (π j))
    (fun i j ↦ IsPullback.of_hasPullback (π i) (π j))
    (isIso_restrictModulePullbackComparison_overPostLift B E h S hS p hp F hbc x _
      (by simpa using inferInstanceAs
        (Flat (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x)))))
      (by simpa using inferInstanceAs
        (LocallyOfFinitePresentation
          (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x))))))
    (fun i ↦ isIso_restrictModulePullbackComparison_overPostLift B E h S hS p hp F hbc x (X i)
      (hflat i) (hlfp i))
    (fun i j ↦ isIso_restrictModulePullbackComparison_overPostLift B E h S hS p hp F hbc x _
      (prop_hom_pullback B _ (π i) (π j) (hflat i) ((hleft j).symm ▸ hflat j))
      (prop_hom_pullback B _ (π i) (π j) (hlfp i) ((hleft j).symm ▸ hlfp j)))
    hcov M

end OfFlat

end Transport

end AlgebraicGeometry.Stack

end
