module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomGluingOnABasis

/-!
# The glueing of derived morphisms over a collection of opens that need not be a basis

Let `(X, 𝒪_X)` be a ringed space and let `ℬ` be a collection of open subsets covering `X` such
that the intersection of two members of `ℬ` is the union of the members of `ℬ` contained in it —
hypothesis (1) of [Stacks, Tag 0D68].  Let `K`, `L` be objects of `D(𝒪_X)` with
`Ext^i(K|_U, L|_U) = 0` for `i < 0` and `U ∈ ℬ`.

`Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_of_isBasis` glues
morphisms over a *basis* of the target of a morphism of ringed spaces.  The members of `ℬ` need
not be a basis of `X`; this file runs that statement through the coarsening of
[Stacks, Tag 0D5Q], exactly as
`Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_of_sSup_covered` does for the vanishing
clause of Tag 0D68.  The coarsening is `Stacks.DerivedGlueing.exists_coarsening`: a continuous
`X ⟶ Z` with `𝒪_Z = f_* 𝒪_X` and, for each member of `ℬ`, an open of `Z` whose inverse image is
that member, the opens so obtained forming a basis of `Z`.

Two pieces of bookkeeping are needed that the vanishing clause did not need.

* The vanishing clause's conclusion is a `Prop`, so it moves along the equality of opens
  `f⁻¹(g W) = W` by a rewrite, whereas a *family of morphisms* has to be transported.  That
  transport is `Stacks.DerivedGlueing.homCastOpen`, and the only lemma about it that is used is
  `Stacks.DerivedGlueing.restrictDerivedHom_homCastOpen`: restriction of morphisms commutes with
  it, which after substituting the two equalities is the statement that two arrows of the poset
  of opens agree — and they do, there being only one.
* `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` exhibits an open that `ℬ` covers as
  an inverse image, but the glueing also needs that the open of `Z` attached to a member below
  `O` is below the open so produced.  The coarse open is the union of exactly those, so that is
  `le_sSup`; it is recorded here as
  `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered'`, a strengthening of the existing
  statement rather than a second construction.  It is needed because the map to the coarse space
  is not known to reflect the order on opens.

## Main definitions

* `Stacks.DerivedGlueing.homCastOpen` — a morphism between the restrictions of two objects to an
  open, transported along an equality of opens.

## Main results

* `Stacks.DerivedGlueing.restrictDerivedHom_homCastOpen` — restriction of morphisms commutes with
  that transport.
* `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered'` — the coarse open, together with
  the fact that it contains the coarse open of every member below `O`.
* `Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_of_sSup_covered` — the glueing of
  morphisms over a collection covering `X` whose pairwise intersections are unions of members,
  over any open that the collection covers.

## What is granted, and why

The hypothesis `hmap` is the restriction compatibility of the identification of the values of the
Hom presheaf of [Stacks, Tag 0D66] part (2) with the groups of morphisms between the restrictions,
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`.  It is
carried universally in the morphism of ringed spaces, because the morphism it is applied to — the
coarsening — is produced existentially and so cannot be named in the statement.  It is the only
hypothesis of the main result that is not a hypothesis of Tag 0D68 itself, and the route for it is
recorded in the section *What is granted, and why* of the module documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution`.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnboundedHigherDirectImage (preimageRestrict
  derivedPreimageCohomologyPresheaf derivedPreimageHomPresheafValueEquiv
  exists_unique_restrictDerivedHom_of_isBasis)
open Stacks.SheafOfModules (homSheafObject ringedSite)

namespace Stacks.DerivedGlueing

universe u

/-! ### The coarse open attached to an open that the collection covers -/

/-- **A coarsening sees every open that is a union of members, and sees the members below it.**
This is `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` together with the statement
that the coarse open of a member contained in `O` is contained in the coarse open produced: the
latter is by construction the union of exactly those, so this is `le_sSup`.

It is needed because the map to the coarse space is not known to reflect the order on opens, so
`f⁻¹(g W) = W ≤ O = f⁻¹ V` does not by itself give `g W ≤ V`. -/
theorem exists_preimage_eq_of_sSup_covered' {T Z : TopCat.{u}} (f : T ⟶ Z) (ℬ : Set (Opens T))
    (g : ℬ → Opens Z) (himage : ∀ W : ℬ, (Opens.map f).obj (g W) = W.1)
    (O : Opens T) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O}) :
    ∃ V : Opens Z, (Opens.map f).obj V = O ∧ ∀ W : ℬ, W.1 ≤ O → g W ≤ V := by
  refine ⟨sSup {V | ∃ W : ℬ, W.1 ≤ O ∧ g W = V}, ?_, fun W hWO => le_sSup ⟨W, hWO, rfl⟩⟩
  refine Opens.ext (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · obtain ⟨V, ⟨W, hWO, rfl⟩, hxV⟩ := Opens.mem_sSup.mp hx
    exact hWO ((himage W).le hxV)
  · rw [hO] at hx
    obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx
    exact Opens.mem_sSup.mpr
      ⟨g ⟨W, hW.1⟩, ⟨⟨W, hW.1⟩, hW.2, rfl⟩, (himage ⟨W, hW.1⟩).ge hxW⟩

section Transport

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}
  (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-! ### Transporting a morphism between restrictions along an equality of opens -/

/-- **A morphism between the restrictions of two objects to an open, read over an equal open.**
Two equal opens give literally equal categories of restricted modules, so a morphism between the
restrictions to one is a morphism between the restrictions to the other. -/
def homCastOpen {A A' : Opens X.carrier} (h : A = A')
    (φ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj L) :
    (SheafOfModules.overFunctor.{u} (structureSheafRing X) A').mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (structureSheafRing X) A').mapDerivedCategory.obj L :=
  h ▸ φ

/-- Transport along the reflexive equality does nothing. -/
@[simp]
theorem homCastOpen_rfl {A : Opens X.carrier}
    (φ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj L) :
    homCastOpen K L rfl φ = φ :=
  rfl

/-- Transport along two equalities of opens is transport along their composite. -/
theorem homCastOpen_trans {A B C : Opens X.carrier} (h₁ : A = B) (h₂ : B = C)
    (φ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj L) :
    homCastOpen K L h₂ (homCastOpen K L h₁ φ) = homCastOpen K L (h₁.trans h₂) φ := by
  subst h₁ h₂
  rfl

/-- **Restriction of morphisms commutes with transport along equalities of opens.**  After
substituting the two equalities both sides are restriction along an arrow of the poset of opens,
and there is only one such arrow. -/
theorem restrictDerivedHom_homCastOpen {A A' B B' : Opens X.carrier} (hA : A = A') (hB : B = B')
    (g : B ⟶ A) (g' : B' ⟶ A')
    (φ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u} (structureSheafRing X) A).mapDerivedCategory.obj L) :
    RingedSite.restrictDerivedHom (ringedSite X.sheaf) g' K L (homCastOpen K L hA φ) =
      homCastOpen K L hB (RingedSite.restrictDerivedHom (ringedSite X.sheaf) g K L φ) := by
  subst hA hB
  obtain rfl : g' = g := Subsingleton.elim _ _
  rfl

/-- **Transport along an equality of opens carries a family's value to its value.**  A family of
morphisms indexed by the opens of a collection takes equal opens to transports of one another,
the index being the only thing the value depends on. -/
theorem homCastOpen_family {ℬ : Set (Opens X.carrier)} {O : Opens X.carrier}
    (φ : ∀ U ∈ ℬ, U ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L))
    {A U : Opens X.carrier} (h : A = U) (hA : A ∈ ℬ) (hAO : A ≤ O) (hU : U ∈ ℬ) (hUO : U ≤ O) :
    homCastOpen K L h (φ A hA hAO) = φ U hU hUO := by
  subst h
  rfl

end Transport

/-! ### Glueing over a collection that covers -/

section Glueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}
  (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **The glueing of derived morphisms over a collection of opens covering the space.**  Let `ℬ`
be a collection of open subsets of `X` covering `X` such that the intersection of two members is
the union of the members contained in it, and let `K`, `L` be objects of `D(𝒪_X)` with
`Ext^i(K|_U, L|_U) = 0` for `i < 0` and every `U ∈ ℬ`.  Then a family of morphisms
`K|_U ⟶ L|_U`, indexed by the members `U` of `ℬ` contained in an open `O` which is the union of
the members it contains, and compatible with restriction between members, comes from a unique
morphism `K|_O ⟶ L|_O`.

The members of `ℬ` need not be a basis; this is
`Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_of_isBasis` read
through the coarsening of [Stacks, Tag 0D5Q], whose images of the members of `ℬ` *are* a basis.
The hypothesis `hmap` is the restriction compatibility of the value identification of Tag 0D66
part (2); see the section *What is granted, and why* of the module documentation. -/
theorem exists_unique_restrictDerivedHom_of_sSup_covered
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (hmap : ∀ (Y : RingedSpace.{u, u}) (f : X ⟶ Y) (V V' : Opens Y.carrier) (hV : V' ≤ V)
      (s : ((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf.obj
        (op V) : Type u)),
      derivedPreimageHomPresheafValueEquiv f K L V'
          (((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L)
              0).presheaf.map hV.hom.op) s) =
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hV.hom) K L
          (derivedPreimageHomPresheafValueEquiv f K L V s))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O})
    (φ : ∀ U ∈ ℬ, U ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L))
    (hφ : ∀ (U U' : Opens X.carrier) (hU : U ∈ ℬ) (hU' : U' ∈ ℬ) (hle : U' ≤ U) (hUO : U ≤ O),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) hle.hom K L (φ U hU hUO) =
        φ U' hU' (hle.trans hUO)) :
    ∃! ψ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L,
      ∀ (U : Opens X.carrier) (hU : U ∈ ℬ) (hUO : U ≤ O),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) hUO.hom K L ψ = φ U hU hUO := by
  obtain ⟨Z, base, imageOpen, himage, hbasis⟩ := exists_coarsening ℬ hcover hinter
  obtain ⟨V₀, rfl, hV₀le⟩ := exists_preimage_eq_of_sSup_covered' base ℬ imageOpen himage O hO
  have hmono : ∀ {V V' : Opens Z}, V' ≤ V →
      (opensMap (pushforwardRingedMap base)).obj V' ≤
        (opensMap (pushforwardRingedMap base)).obj V := fun h => (Opens.map _).monotone h
  have heq : ∀ (V : Opens Z) (hV : V ∈ Set.range imageOpen),
      (opensMap (pushforwardRingedMap base)).obj V = (hV.choose).1 := fun V hV =>
    (congrArg (opensMap (pushforwardRingedMap base)).obj hV.choose_spec.symm).trans
      (himage hV.choose)
  have hleO : ∀ (V : Opens Z) (hV : V ∈ Set.range imageOpen), V ≤ V₀ →
      (hV.choose).1 ≤ (Opens.map base).obj V₀ :=
    fun V hV hVV₀ => (heq V hV).symm.trans_le (hmono hVV₀)
  have hpickle : ∀ (V V' : Opens Z) (hV : V ∈ Set.range imageOpen)
      (hV' : V' ∈ Set.range imageOpen), V' ≤ V → (hV'.choose).1 ≤ (hV.choose).1 :=
    fun V V' hV hV' hle => (heq V' hV').symm.trans_le ((hmono hle).trans_eq (heq V hV))
  have hExtB : ∀ V ∈ Set.range imageOpen, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((preimageRestrict (pushforwardRingedMap base) V).obj K)
      ((preimageRestrict (pushforwardRingedMap base) V).obj L) i) := by
    intro V hV i hi
    have h := hExt (hV.choose).1 (hV.choose).2 i hi
    rwa [← heq V hV] at h
  have hφB : ∀ (V V' : Opens Z) (hV : V ∈ Set.range imageOpen)
      (hV' : V' ∈ Set.range imageOpen) (hle : V' ≤ V) (hVV₀ : V ≤ V₀),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf)
          ((opensMap (pushforwardRingedMap base)).map hle.hom) K L
          (homCastOpen K L (heq V hV).symm
            (φ (hV.choose).1 (hV.choose).2 (hleO V hV hVV₀))) =
        homCastOpen K L (heq V' hV').symm
          (φ (hV'.choose).1 (hV'.choose).2 (hleO V' hV' (hle.trans hVV₀))) :=
    fun V V' hV hV' hle hVV₀ =>
      (restrictDerivedHom_homCastOpen K L (heq V hV).symm (heq V' hV').symm
        (hpickle V V' hV hV' hle).hom ((opensMap (pushforwardRingedMap base)).map hle.hom)
          _).trans
        (congrArg (homCastOpen K L (heq V' hV').symm)
          (hφ (hV.choose).1 (hV'.choose).1 (hV.choose).2 (hV'.choose).2
            (hpickle V V' hV hV' hle) (hleO V hV hVV₀)))
  obtain ⟨ψ, hψ, huniq⟩ := exists_unique_restrictDerivedHom_of_isBasis
    (pushforwardRingedMap base) hbasis K L hExtB
    (hmap (pushforwardRingedSpace base) (pushforwardRingedMap base)) V₀
    (fun V hV hVV₀ =>
      homCastOpen K L (heq V hV).symm (φ (hV.choose).1 (hV.choose).2 (hleO V hV hVV₀))) hφB
  refine ⟨ψ, fun U hU hUO => ?_, fun ψ' hψ' => huniq ψ' fun V hV hVV₀ =>
    (restrictDerivedHom_homCastOpen K L rfl (heq V hV).symm (hleO V hV hVV₀).hom
      ((opensMap (pushforwardRingedMap base)).map hVV₀.hom) ψ').trans
      (congrArg (homCastOpen K L (heq V hV).symm) (hψ' _ (hV.choose).2 (hleO V hV hVV₀)))⟩
  have hVmem : imageOpen ⟨U, hU⟩ ∈ Set.range imageOpen := ⟨⟨U, hU⟩, rfl⟩
  have hVV₀ : imageOpen ⟨U, hU⟩ ≤ V₀ := hV₀le ⟨U, hU⟩ hUO
  exact (restrictDerivedHom_homCastOpen K L rfl (himage ⟨U, hU⟩)
        ((opensMap (pushforwardRingedMap base)).map hVV₀.hom) hUO.hom ψ).trans
    ((congrArg (homCastOpen K L (himage ⟨U, hU⟩)) (hψ (imageOpen ⟨U, hU⟩) hVmem hVV₀)).trans
      ((homCastOpen_trans K L (heq (imageOpen ⟨U, hU⟩) hVmem).symm (himage ⟨U, hU⟩) _).trans
        (homCastOpen_family K L φ _ _ _ hU hUO)))

end Glueing

end Stacks.DerivedGlueing

end
