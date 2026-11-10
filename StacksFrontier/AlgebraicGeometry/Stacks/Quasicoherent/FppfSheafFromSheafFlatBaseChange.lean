module

public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsCocycleSheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty

/-!
# Stacks 076T under the source's hypothesis

**Stacks 076T** says that a presheaf of `𝒪_𝒳`-modules `F` which is locally quasi-coherent
(**Stacks 06WJ**) and whose comparison maps `c_φ` of **Stacks 06WC** are isomorphisms along the
arrows lying over a flat morphism locally of finite presentation is a sheaf for the fppf topology.
In the source the comparison map is a map of *sheaves*, out of the inverse image of sheaves of
modules. `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange`
proves the lemma under the stronger hypothesis that the comparison map of presheaves be
invertible; this file proves it under the source's hypothesis,
`AlgebraicGeometry.Stack.HasSheafFlatLfpBaseChangeProperty`: the comparison map of presheaves is a
local isomorphism, equivalently the comparison map of sheaves is an isomorphism.

The proof is the one of the presheaf-level version, with the identification of sections of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsSheafified.lean` and its
cocycle
condition of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleSheafified.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.HasSheafFlatLfpBaseChangeProperty`: hypothesis (b) of
  **Stacks 076T**.

## Main results

* `AlgebraicGeometry.Stack.isIsoSheafifiedComparison_of_isLocallyBijective`: a comparison map of
  presheaves which is a local isomorphism has an invertible adjunct.
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange`:
  **Stacks 076T.**
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange`:
  **Stacks 0771, part (1).**
* `AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`: the object of `Mod(𝒪_𝒳)` a member of
  `LQCoh^fbc(𝒪_𝒳)` is, for an algebraic stack.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
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

/-- **Hypothesis (b) of Stacks 076T**, in the source's reading: along every arrow `φ` of `𝒳`
lying over a morphism of schemes which is flat and locally of finite presentation, the comparison
map `c_φ` of **Stacks 06WC** is a local isomorphism of the small étale site — locally injective
and locally surjective — that is, the comparison map of sheaves of modules is an isomorphism. -/
abbrev HasSheafFlatLfpBaseChangeProperty : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left) →
      Presheaf.IsLocallyInjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B) F)) ∧
        Presheaf.IsLocallySurjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B) F))

/-- The flat base change property of **Stacks 0762** implies hypothesis (b) of
**Stacks 076T**, which asks the same of fewer arrows. -/
theorem hasSheafFlatLfpBaseChangeProperty_of_hasSheafFlatBaseChangeProperty
    (hF : HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F) :
    HasSheafFlatLfpBaseChangeProperty B E h S hS p hp F :=
  fun φ hflat _ => hF φ hflat

section Comparison

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- **A comparison map which is a local isomorphism has an invertible adjunct.** If the
comparison map `c_φ` of **Stacks 06WC** is locally injective and locally surjective, its
sheafification is an isomorphism (the sheafification of the underlying abelian presheaves is, and
forgetting the module structure reflects isomorphisms), and so is its adjunct under the
sheafification adjunction, the counit being invertible. -/
theorem isIsoSheafifiedComparison_of_isLocallyBijective {x z : 𝒳} (φ : z ⟶ x)
    (h₁ : Presheaf.IsLocallyInjective
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F)))
    (h₂ : Presheaf.IsLocallySurjective
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F))) :
    IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ := by
  have hW : IsIso ((presheafToSheaf
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F))) := by
    rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]
    exact ⟨h₁, h₂⟩
  have hsh : IsIso ((PresheafOfModules.sheafification
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj)).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F)) := by
    have : IsIso ((SheafOfModules.toSheaf _).map ((PresheafOfModules.sheafification
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F))) := hW
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have e := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj)).homEquiv_counit
    (Y := restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F z (hlqc.2 z).choose)
    (g := restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)
  unfold IsIsoSheafifiedComparison sheafifiedRestrictComparison
  rw [e]
  exact IsIso.comp_isIso' hsh (NatIso.isIso_app_of_isIso _ _)

/-- **Hypothesis (b) of Stacks 076T at one object of the big fppf site of `U`**: the comparison
map of sheaves of **Stacks 06WC** is an isomorphism along the arrow of `𝒳` which the localization
equivalence of **Stacks 06W0** produces over an object of the big fppf site of the scheme below
`x` lying over a flat morphism locally of finite presentation. -/
theorem isIsoSheafifiedComparison_overPostLift
    (hbc : HasSheafFlatLfpBaseChangeProperty B E h S hS p hp F)
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hflat : Flat (B.inclusion.map V.hom))
    (hlfp : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V) :=
  have hb := hbc _ (flat_overPostLift B S hS p hp x V hflat)
    (locallyOfFinitePresentation_overPostLift B S hS p hp x V hlfp)
  isIsoSheafifiedComparison_of_isLocallyBijective B E h S hS p hp F hlqc _ hb.1 hb.2

end Comparison

namespace QuasicoherentBelow

variable {B E h S hS p hp F} {x : 𝒳} (d : QuasicoherentBelow B E h S hS p hp F x)


/-- The identification of the sections of `AlgebraicGeometry.Stack.overPostSectionsMapSheafified`
at the quasi-coherent module below `x`. -/
noncomputable def sectionsMapSheafified (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).obj (op V) :=
  overPostSectionsMapSheafified B E h S hS p hp F hlqc x V d.val d.isQuasicoherent d.isSheaf d.iso
      hiso M

/-- **`AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapSheafified` is a bijection.** -/
theorem sectionsMapSheafified_bijective (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (d.sectionsMapSheafified hlqc V hiso M) :=
  overPostSectionsMapSheafified_bijective B E h S hS p hp F hlqc x V d.val d.isQuasicoherent
      d.isSheaf
    d.iso hiso M

/-- **Over the cocycle condition,
`AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapSheafified` commutes with the restriction
maps of the big fppf site of `U`.** -/
theorem sectionsMapSheafified_naturality (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hcoc : LiftedSectionsCocycleSheafified B E h S hS p hp)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V'))
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    d.sectionsMapSheafified hlqc V' hiso' M ((overPostTransportSections B S hS p hp F x M).map r.op
        s) =
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).map r.op
        (d.sectionsMapSheafified hlqc V hiso M s) :=
  overPostSectionsMapSheafified_naturality B E h S hS p hp F hlqc hcoc x r d.val d.isQuasicoherent
    d.isSheaf d.iso hiso hiso' M s

end QuasicoherentBelow

section Transport

attribute [local irreducible] overPostTransportSections overPostSectionsTypes
  QuasicoherentBelow.sectionsMapSheafified

/-! ### The transport, downstairs on the big fppf site of `U` -/

section OfIsIso

/-- **The transport of the sheaf condition downstairs, over the isomorphisms hypothesis (b)
supplies.**

Let `{π i : U_i / U → U / U}` be a family of arrows of the big fppf site of the scheme `U` below
`x` which generates a covering sieve, with prescribed fibre products `W i j`, and suppose the
comparison map `c_φ` of **Stacks 06WC** is an isomorphism along the arrows of `𝒳` which the
localization equivalence of **Stacks 06W0** produces over `U / U`, over each `U_i / U` and over
each `W i j`. Then the transported presheaf
`AlgebraicGeometry.Stack.overPostTransportSections` satisfies the sheaf condition for the family.

This is `CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps`, fed the identification of
`AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapSheafified` at those objects — a bijection
over
`U / U`, an injection over each `U_i / U`, a bare function over each `W i j`, with the three
compatibilities of `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapSheafified_naturality` —
and the
sheaf condition for `𝒢^a` of
`AlgebraicGeometry.Stack.QuasicoherentBelow.isSheafFor_sectionsTypes`, which is Descent,
**Stacks 03DT**.

The three isomorphisms are asked for one object at a time, and at no other object of the slice is
anything assumed: an identification of the two presheaves over the whole slice would be clause
(b) of **Stacks 06WK**, strictly stronger than hypothesis (b) of Stacks 076T. -/
theorem isSheafFor_overPostTransportSections_of_isIsoSheafified
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hcoc : LiftedSectionsCocycleSheafified B E h S hS p hp) {x : 𝒳}
    (d : QuasicoherentBelow B E h S hS p hp F x)
    {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
    {W : I → I → Over ((p ⋙ Over.forget (B.obj hS)).obj x)}
    (pr₁ : ∀ i j, W i j ⟶ X i) (pr₂ : ∀ i j, W i j ⟶ X j)
    (hW : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (π i) (π j))
    (hisoY : IsIsoSheafifiedComparison B E h S hS p hp F hlqc
      (overPostLiftHom B S hS p hp x (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))))
    (hisoX : ∀ i, IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x (X
    i)))
    (hisoW : ∀ i j, IsIsoSheafifiedComparison B E h S hS p hp F hlqc
      (overPostLiftHom B S hS p hp x (W i j)))
    (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
    BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
    (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp F x M)
      (Presieve.ofArrows X π) :=
  Presieve.Arrows.isSheafFor_ofArrows_of_maps
    (Q := overPostTransportSections B S hS p hp F x M)
    (Q' := overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M)
    (Y := Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) (X := X) (W := W)
    π pr₁ pr₂ hW
    (d.sectionsMapSheafified hlqc (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) hisoY M)
    (d.sectionsMapSheafified_bijective hlqc (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) hisoY
        M)
    (fun i ↦ d.sectionsMapSheafified hlqc (X i) (hisoX i) M)
    (fun i ↦ (d.sectionsMapSheafified_bijective hlqc (X i) (hisoX i) M).injective)
    (fun i j ↦ d.sectionsMapSheafified hlqc (W i j) (hisoW i j) M)
    (fun i s ↦ d.sectionsMapSheafified_naturality hlqc hcoc (π i) hisoY (hisoX i) M s)
    (fun i j s ↦ d.sectionsMapSheafified_naturality hlqc hcoc (pr₁ i j) (hisoX i) (hisoW i j) M s)
    (fun i j s ↦ d.sectionsMapSheafified_naturality hlqc hcoc (pr₂ i j) (hisoX j) (hisoW i j) M s)
    (d.isSheafFor_sectionsTypes X π hcov M)

end OfIsIso

section OfFlat

/-- **The sheaf condition along a family lying over an fppf covering of schemes, transported
downstairs from Descent, Stacks 03DT.**

`AlgebraicGeometry.Stack.isSheafFor_overPostTransportSections_of_isIsoSheafified` at the fibre
products of
the big fppf site of `U`, with the three families of isomorphisms supplied by hypothesis (b) of
**Stacks 076T**: the objects `U / U`, `U_i / U` and `(U_i ×_U U_j) / U` all lie over a flat
morphism locally of finite presentation as soon as the `U_i → U` do — the first because it lies
over an identity, the last by `AlgebraicGeometry.prop_hom_pullback`, a fibre product projection
being a base change — and
`AlgebraicGeometry.Stack.isIsoSheafifiedComparison_overPostLift` turns that into the
isomorphism of the comparison map along the arrow of `𝒳` above. -/
theorem isSheafFor_overPostTransportSectionsSheafified
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasSheafFlatLfpBaseChangeProperty B E h S hS p hp F)
    (hcoc : LiftedSectionsCocycleSheafified B E h S hS p hp) {x : 𝒳}
    (d : QuasicoherentBelow B E h S hS p hp F x)
    {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
    (hflat : ∀ i, Flat (B.inclusion.map (X i).hom))
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (X i).hom))
    (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
    BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
    (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp F x M)
      (Presieve.ofArrows X π) := by
  have hleft : ∀ i, (π i).left = (X i).hom := fun i ↦ by simpa using Over.w (π i)
  exact isSheafFor_overPostTransportSections_of_isIsoSheafified B E h S hS p hp F hlqc hcoc d X π
    (fun i j ↦ pullback.fst (π i) (π j)) (fun i j ↦ pullback.snd (π i) (π j))
    (fun i j ↦ IsPullback.of_hasPullback (π i) (π j))
    (isIsoSheafifiedComparison_overPostLift B E h S hS p hp F hlqc hbc x _
      (by simpa using inferInstanceAs
        (Flat (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x)))))
      (by simpa using inferInstanceAs
        (LocallyOfFinitePresentation
          (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x))))))
    (fun i ↦ isIsoSheafifiedComparison_overPostLift B E h S hS p hp F hlqc hbc x (X i)
      (hflat i) (hlfp i))
    (fun i j ↦ isIsoSheafifiedComparison_overPostLift B E h S hS p hp F hlqc hbc x _
      (prop_hom_pullback B _ (π i) (π j) (hflat i) ((hleft j).symm ▸ hflat j))
      (prop_hom_pullback B _ (π i) (π j) (hlfp i) ((hleft j).symm ▸ hlfp j)))
    hcov M

end OfFlat

end Transport

/-- **The step of the proof of Stacks 076T**, in the source's reading of hypothesis (b): for a
presheaf of modules which is locally quasi-coherent and satisfies
`AlgebraicGeometry.Stack.HasSheafFlatLfpBaseChangeProperty`, the sheaf condition along every
family of arrows of `𝒳` which generates a covering sieve of the inherited fppf topology and lies
over an fppf covering of schemes. -/
abbrev IsSheafForLiftedFppfFamilySheafified : Prop :=
  ∀ F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj,
    IsLocallyQuasicoherent B E h S hS p hp F →
    HasSheafFlatLfpBaseChangeProperty B E h S hS p hp F →
    ∀ ⦃x : 𝒳⦄ (R : Presieve x),
      Sieve.generate R ∈ associatedTopology B S hS p B.topology x →
      (∀ ⦃z : 𝒳⦄ (φ : z ⟶ x), R φ → Flat (B.inclusion.map (p.map φ).left) ∧
        LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left)) →
      ∀ M : AddCommGrpCat.{u}, Presieve.IsSheafFor (F.presheaf ⋙ coyoneda.obj (op M)) R

/-- **The step of Stacks 076T, under the cocycle condition**, in the source's reading of
hypothesis (b). -/
theorem isSheafForLiftedFppfFamilySheafified (hcoc : LiftedSectionsCocycleSheafified B E h S hS p
    hp) :
    IsSheafForLiftedFppfFamilySheafified B E h S hS p hp := by
  intro F hlqc hbc x R hR hfl M
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc x
  obtain ⟨I, z, φ, hRe⟩ :
      ∃ (I : Type (max v w)) (z : I → 𝒳) (φ : ∀ i, z i ⟶ x), Presieve.ofArrows z φ = R := by
    refine ⟨(y : 𝒳) × {f : y ⟶ x // R f}, fun i ↦ i.1, fun i ↦ i.2.1, ?_⟩
    funext Z g
    refine propext ⟨?_, fun hg ↦ ?_⟩
    · rintro ⟨i⟩
      exact i.2.2
    · exact Presieve.ofArrows.mk (⟨Z, g, hg⟩ : (y : 𝒳) × {f : y ⟶ x // R f})
  have hmem : ∀ i, R (φ i) := fun i ↦ hRe ▸ Presieve.ofArrows.mk i
  have hflat : ∀ i, Flat (B.inclusion.map (p.map (φ i)).left) := fun i ↦ (hfl (φ i) (hmem i)).1
  have hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (p.map (φ i)).left) := fun i ↦
    (hfl (φ i) (hmem i)).2
  have : p.IsFibered := hp.isFibered
  rw [← hRe] at hR ⊢
  have hbase : Sieve.ofArrows (fun i ↦ p.obj (z i)) (fun i ↦ p.map (φ i)) ∈
      (B.topology.over (B.obj hS)) (p.obj x) :=
    (Functor.isInheritedTopology_inheritedTopology.{max v w} p (B.topology.over (B.obj hS))
      z φ fun i ↦ hp.isStronglyCartesian (φ i)).1 hR
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hbase
  rw [isSheafFor_ofArrows_iff_overPost B S hS p hp x (F.presheaf ⋙ coyoneda.obj (op M))
    (overPostTransportSections B S hS p hp F x M) φ
    (overPostTransportIso B S hS p hp x (F.presheaf ⋙ coyoneda.obj (op M)))]
  refine isSheafFor_overPostTransportSectionsSheafified B E h S hS p hp F hlqc hbc hcoc d _ _ hflat
      hlfp
    ?_ M
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hbase

/-- **Stacks 076T.** Let `F` be a presheaf of modules over the structure sheaf of a category
fibred in groupoids over the big fppf category of schemes over `S`. If `F` is locally
quasi-coherent (**Stacks 06WJ**) and the comparison map `c_φ` of **Stacks 06WC** is an
isomorphism of sheaves — a local isomorphism of the small étale site — for every arrow of `𝒳`
lying over a morphism of schemes which is flat and locally of finite presentation, then `F` is a
sheaf for the fppf topology of **Stacks 06TP**. -/
theorem isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasSheafFlatLfpBaseChangeProperty B E h S hS p hp F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_of_isSheafFor_flatLfp B S hS p hp F.presheaf
    fun {_} R hR hflat => isSheafForLiftedFppfFamilySheafified B E h S hS p hp
      (liftedSectionsCocycleSheafified B E h S hS p hp) F hlqc hbc R hR hflat

/-- **Stacks 0771, part (1).** A presheaf of modules over the structure sheaf of a category
fibred in groupoids over the big fppf site which lies in `LQCoh^fbc(𝒪_𝒳)` — locally
quasi-coherent (**Stacks 06WJ**) with the flat base change property of **Stacks 0762** — is a
sheaf for the fppf topology of **Stacks 06TP**.

This is **Stacks 076T**,
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange`, whose
hypothesis (b) asks the flat base change property of fewer arrows. The module sections are in the
universe of the schemes; the statement holds for every category fibred in groupoids, which
generalizes the source's algebraic stack. -/
@[stacks 0771 "part (1): a member of LQCoh^fbc (with the flat base change property of 0762 read \
  on sheaves) is a sheaf for the fppf topology; for every category fibred in groupoids"]
theorem isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange B E h S hS p hp F hF.1
    (hasSheafFlatLfpBaseChangeProperty_of_hasSheafFlatBaseChangeProperty B E h S hS p hp F hF.2)

/-- **Stacks 0771, part (1)**, the clause "it is an object of `Mod(𝒪_𝒳)`": a member of
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_ét, 𝒪_𝒳)` on an algebraic stack is a module on the fppf site, with the
same underlying presheaf of modules, and it lies in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. -/
@[stacks 0771 "part (1), the clause `i.e. it is an object of Mod(𝒪_𝒳)`: the fppf module a member \
  of LQCoh^fbc is, again in LQCoh^fbc"]
noncomputable def fppfModuleOfLqcohSheafFbc (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)))
    (hG : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 G) :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory :=
  ⟨⟨G.val, isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids G.val hG⟩, hG⟩

/-- The fppf module of `AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc` has the given
presheaf of modules underneath it. -/
@[simp]
theorem fppfModuleOfLqcohSheafFbc_val (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)))
    (hG : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 G) :
    (fppfModuleOfLqcohSheafFbc B E h S hS 𝒳 G hG).obj.val = G.val :=
  rfl


end AlgebraicGeometry.Stack

end
