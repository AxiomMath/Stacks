module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExtNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTStructure
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemHom
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingTransfer

/-!
# The core case of Stacks 0G2H, from `Ext`-groups to `RestrictionLifting`

Let `Φ : 𝒜 ⥤ ℬ` be an exact functor of abelian categories, let `S : ℕᵒᵖ ⥤ 𝒜` be an inverse
sequence and let `B` be an object of `𝒜`. This file translates the assertion

`colim_n Ext^i_𝒜(S_n, B) = Ext^i_ℬ(Φ S_n, Φ B)`

— in the elementwise form the first display of [Stacks, Tag 01YB] and its `i > 0` analogue are
stated at — into `CategoryTheory.RestrictionLifting` for the system `(S_n[p])` of objects of
`D(𝒜)` concentrated in the single degree `p` against the target `B[q]`, where `q + i = p`. That
`RestrictionLifting` statement is the core case of [Stacks, Tag 0G2H], the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`.

The translation is the identification `DerivedCategory.singleHomEquivExt` of the morphisms of
`D(𝒜)` between single-degree objects with `Ext`-groups, together with its two compatibilities
proved in `StacksFrontier/Algebra/Homology/DerivedCategory/SingleDegreeExtNaturality.lean`:
naturality in the source turns the transition maps of `(S_n)` into Yoneda composition with
`CategoryTheory.Abelian.Ext.mk₀`, and compatibility with an exact functor turns
`Φ.mapDerivedCategory` on morphisms into `CategoryTheory.Abelian.Ext.mapExactFunctor` on
classes. The source and target of a morphism are transported by
`CategoryTheory.Functor.mapSingleFunctorIso`.

For `p < q` there is nothing to translate: all the `Hom`-groups involved vanish
(`DerivedCategory.hom_singleFunctor_obj_eq_zero`), on both sides of `Φ`, so the statement is
automatic.

## Main results

* `CategoryTheory.restrictionLifting_singleFunctor_of_ext`: **the core case of
  [Stacks, Tag 0G2H] in the `RestrictionLifting` language, from the `Ext`-colimit statement.**
* `CategoryTheory.restrictionLifting_singleFunctor_of_lt`: the same for `p < q`, where it is
  automatic.
* `AlgebraicGeometry.restrictionLifting_of_singleFunctor_presentation` and
  `AlgebraicGeometry.restrictionLifting_of_singleFunctor_proIso`: the statement for a system in
  `D^b_{Coh}(𝒪_X)` and a target there, from the statement in `D(𝒪_X)` for the presentations of
  both by single-degree objects, the source presentation being an isomorphism of systems in the
  first and only a pro-isomorphism in the second.
* `AlgebraicGeometry.exists_isCoherent_iso_singleFunctor_obj`: the presentation of the target —
  an object of `D^b_{Coh}(𝒪_X)` concentrated in degree `q` is a coherent module in degree `q`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open InverseSequence

universe w t v v₁ v₂ u u'

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v₁} 𝒜] [Abelian 𝒜] {ℬ : Type u'} [Category.{v₂} ℬ] [Abelian ℬ]
  [HasDerivedCategory.{v} 𝒜] [HasDerivedCategory.{v} ℬ]
  (Φ : 𝒜 ⥤ ℬ) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- Conjugating a morphism of `D(ℬ)` by `CategoryTheory.Functor.mapSingleFunctorIso` is
injective, being a bijection. -/
private lemma conj_injective (Y B : 𝒜) (p q : ℤ) :
    Function.Injective (fun z : Φ.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 p).obj Y)
        ⟶ Φ.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 q).obj B) =>
      (Φ.mapSingleFunctorIso p).inv.app Y ≫ z ≫ (Φ.mapSingleFunctorIso q).hom.app B) :=
  (Iso.homCongr ((Φ.mapSingleFunctorIso p).app Y) ((Φ.mapSingleFunctorIso q).app B)).injective

/-- The naturality of `CategoryTheory.Functor.mapSingleFunctorIso` in the source, in the form the
transition maps of an inverse sequence are read through. -/
private lemma mapSingleFunctorIso_inv_naturality (p : ℤ) {Y Z : 𝒜} (u : Y ⟶ Z) :
    (DerivedCategory.singleFunctor ℬ p).map (Φ.map u) ≫
        (Φ.mapSingleFunctorIso p).inv.app Z =
      (Φ.mapSingleFunctorIso p).inv.app Y ≫
        Φ.mapDerivedCategory.map ((DerivedCategory.singleFunctor 𝒜 p).map u) :=
  (Φ.mapSingleFunctorIso p).inv.naturality u

variable [HasExt.{w} 𝒜] [HasExt.{t} ℬ]

/-- **The core case of [Stacks, Tag 0G2H], from the `Ext`-colimit statement.** Let `Φ` be an
exact functor, `(S_n)` an inverse sequence, `B` an object, and `q + i = p`. If every class in
`Ext^i_ℬ(Φ S_n, Φ B)` comes, past some stage, from a class in `Ext^i_𝒜(S_m, B)`, and two classes
in `Ext^i_𝒜(S_n, B)` with the same image under `Φ` agree past some stage, then `Φ` satisfies the
identification of [Stacks, Tag 0G2H] for the system `(S_n[p])` against the target `B[q]`. -/
public lemma restrictionLifting_singleFunctor_of_ext (S : ℕᵒᵖ ⥤ 𝒜) (B : 𝒜) (p q : ℤ) (i : ℕ)
    (hi : q + (i : ℤ) = p)
    (hlift : ∀ (n : ℕ) (η : Ext.{t} (Φ.obj (S.obj (op n))) (Φ.obj B) i),
      ∃ (m : ℕ) (h : n ≤ m) (ξ : Ext.{w} (S.obj (op m)) B i),
        ξ.mapExactFunctor Φ = (Ext.mk₀ (Φ.map (tr S h))).comp η (zero_add i))
    (heq : ∀ (n : ℕ) (ξ ξ' : Ext.{w} (S.obj (op n)) B i),
      ξ.mapExactFunctor Φ = ξ'.mapExactFunctor Φ →
      ∃ (m : ℕ) (h : n ≤ m), (Ext.mk₀ (tr S h)).comp ξ (zero_add i) =
        (Ext.mk₀ (tr S h)).comp ξ' (zero_add i)) :
    RestrictionLifting (S ⋙ DerivedCategory.singleFunctor 𝒜 p) Φ.mapDerivedCategory
      ((DerivedCategory.singleFunctor 𝒜 q).obj B) := by
  constructor
  · intro n g
    obtain ⟨m, h, ξ, hξ⟩ := hlift n (DerivedCategory.singleHomEquivExt
      (Φ.obj (S.obj (op n))) (Φ.obj B) p q i hi
      ((Φ.mapSingleFunctorIso p).inv.app (S.obj (op n)) ≫ g ≫
        (Φ.mapSingleFunctorIso q).hom.app B))
    refine ⟨m, h, (DerivedCategory.singleHomEquivExt (S.obj (op m)) B p q i hi).symm ξ, ?_⟩
    refine conj_injective Φ (S.obj (op m)) B p q ?_
    dsimp only
    rw [Φ.mapSingleFunctorIso_conj_singleHomEquivExt_symm (S.obj (op m)) B p q i hi ξ, hξ]
    show _ = (Φ.mapSingleFunctorIso p).inv.app (S.obj (op m)) ≫
      (Φ.mapDerivedCategory.map ((DerivedCategory.singleFunctor 𝒜 p).map (tr S h)) ≫ g) ≫ _
    rw [Category.assoc, ← reassoc_of% (mapSingleFunctorIso_inv_naturality Φ p (tr S h)),
      DerivedCategory.singleHomEquivExt_symm_mk₀_comp, Equiv.symm_apply_apply]
  · intro n f g hfg
    have hext : (DerivedCategory.singleHomEquivExt (S.obj (op n)) B p q i hi f).mapExactFunctor Φ =
        (DerivedCategory.singleHomEquivExt (S.obj (op n)) B p q i hi g).mapExactFunctor Φ := by
      refine (DerivedCategory.singleHomEquivExt (Φ.obj (S.obj (op n))) (Φ.obj B)
        p q i hi).symm.injective ?_
      rw [← Φ.mapSingleFunctorIso_conj_singleHomEquivExt_symm, ←
        Φ.mapSingleFunctorIso_conj_singleHomEquivExt_symm, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply, hfg]
    obtain ⟨m, h, he⟩ := heq n _ _ hext
    refine ⟨m, h, (DerivedCategory.singleHomEquivExt (S.obj (op m)) B p q i hi).injective ?_⟩
    rwa [show tr (S ⋙ DerivedCategory.singleFunctor 𝒜 p) h =
        (DerivedCategory.singleFunctor 𝒜 p).map (tr S h) from rfl,
      DerivedCategory.singleHomEquivExt_singleFunctor_map_comp,
      DerivedCategory.singleHomEquivExt_singleFunctor_map_comp]

omit [HasExt.{w} 𝒜] [HasExt.{t} ℬ] in
/-- **The core case of [Stacks, Tag 0G2H] for `p < q`**, where it is automatic: in Mathlib's
conventions `Hom_{D(𝒜)}(A[p], B[q])` vanishes for `p < q`, and so does its counterpart in
`D(ℬ)`. -/
public lemma restrictionLifting_singleFunctor_of_lt (S : ℕᵒᵖ ⥤ 𝒜) (B : 𝒜) (p q : ℤ)
    (hpq : p < q) :
    RestrictionLifting (S ⋙ DerivedCategory.singleFunctor 𝒜 p) Φ.mapDerivedCategory
      ((DerivedCategory.singleFunctor 𝒜 q).obj B) := by
  have hzero : ∀ (Y : 𝒜) (z : Φ.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor 𝒜 p).obj Y) ⟶
      Φ.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 q).obj B)), z = 0 := by
    intro Y z
    refine conj_injective Φ Y B p q ?_
    dsimp only
    rw [DerivedCategory.hom_singleFunctor_obj_eq_zero (Φ.obj Y) (Φ.obj B) p q hpq
      ((Φ.mapSingleFunctorIso p).inv.app Y ≫ z ≫ (Φ.mapSingleFunctorIso q).hom.app B)]
    simp
  constructor
  · intro n g
    refine ⟨n, le_rfl, 0, ?_⟩
    rw [Φ.mapDerivedCategory.map_zero, hzero _ g, Limits.comp_zero]
  · intro n f g _
    refine ⟨n, le_rfl, ?_⟩
    rw [DerivedCategory.hom_singleFunctor_obj_eq_zero _ B p q hpq f,
      DerivedCategory.hom_singleFunctor_obj_eq_zero _ B p q hpq g]

end CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **The core case of [Stacks, Tag 0G2H] in `D^b_{Coh}(𝒪_X)`, from the core case in `D(𝒪_X)`.**
Let `(G_n)` be an inverse sequence in `D^b_{Coh}(𝒪_X)` and `L` an object of it, and suppose given
presentations of `(G_n)` as a system `(S_n[p])` of single-degree objects of `D(𝒪_X)` and of `L` as
`B[q]`. Then the identification for `(S_n[p])` against `B[q]` and restriction along `j` gives the
identification for `(G_n)` against `L` and `AlgebraicGeometry.restrictBoundedCoherent`.

`AlgebraicGeometry.restrictBoundedCoherent j` *is*
`(boundedCoherentDerived X).ι ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory`, so this
is `CategoryTheory.RestrictionLifting.of_fullyFaithful_comp` for the fully faithful inclusion of
`D^b_{Coh}(𝒪_X)`, after transporting the source system by the first presentation and the target
object by the second. -/
public lemma restrictionLifting_of_singleFunctor_presentation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (G : ℕᵒᵖ ⥤ BoundedCoherentDerived X) (L : BoundedCoherentDerived X)
    (p q : ℤ) (S : ℕᵒᵖ ⥤ X.Modules) (B : X.Modules)
    (eS : G ⋙ (boundedCoherentDerived X).ι ≅ S ⋙ DerivedCategory.singleFunctor X.Modules p)
    (eL : (boundedCoherentDerived X).ι.obj L ≅ (DerivedCategory.singleFunctor X.Modules q).obj B)
    (h : RestrictionLifting (S ⋙ DerivedCategory.singleFunctor X.Modules p)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory
      ((DerivedCategory.singleFunctor X.Modules q).obj B)) :
    RestrictionLifting G (restrictBoundedCoherent j) L :=
  RestrictionLifting.of_fullyFaithful_comp G (boundedCoherentDerived X).ι
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory L
    (RestrictionLifting.of_natIso eS _ _ (h.of_iso_target eL.symm))

/-- **The core case of [Stacks, Tag 0G2H] in `D^b_{Coh}(𝒪_X)`, from a *pro*-presentation of the
source system.** The source system of the tag is only pro-isomorphic to the ideal-power system of
its cohomology — that is what the 0G4R pro-isomorphism
`Stacks.Duality.cohomologyIdealPowersProIso_comp` provides — so this is the form the dévissage
uses. -/
public lemma restrictionLifting_of_singleFunctor_proIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (G : ℕᵒᵖ ⥤ BoundedCoherentDerived X) (L : BoundedCoherentDerived X)
    (p q : ℤ) (S : ℕᵒᵖ ⥤ X.Modules) (B : X.Modules)
    (eS : ProIso (G ⋙ (boundedCoherentDerived X).ι)
      (S ⋙ DerivedCategory.singleFunctor X.Modules p))
    (eL : (boundedCoherentDerived X).ι.obj L ≅ (DerivedCategory.singleFunctor X.Modules q).obj B)
    (h : RestrictionLifting (S ⋙ DerivedCategory.singleFunctor X.Modules p)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory
      ((DerivedCategory.singleFunctor X.Modules q).obj B)) :
    RestrictionLifting G (restrictBoundedCoherent j) L :=
  RestrictionLifting.of_fullyFaithful_comp G (boundedCoherentDerived X).ι
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory L
    (RestrictionLifting.of_proIso eS _ _ (h.of_iso_target eL.symm))

/-- **An object of `D^b_{Coh}(𝒪_X)` concentrated in the single degree `q` is a coherent module
placed in degree `q`.** This is the presentation of the *target* that
`AlgebraicGeometry.restrictionLifting_of_singleFunctor_proIso` consumes: it is
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE` read through
`CategoryTheory.ObjectProperty.tStructure_isGE_iff`, and the module is coherent because it is
isomorphic to `H^q` of the object, which is coherent by definition of `D^b_{Coh}`. -/
public lemma exists_isCoherent_iso_singleFunctor_obj {X : Scheme.{u}}
    (L : BoundedCoherentDerived X) (q : ℤ)
    (hGE : (boundedCoherentTStructure X).IsGE L q)
    (hLE : (boundedCoherentTStructure X).IsLE L q) :
    ∃ B : X.Modules, B.IsCoherent ∧ Nonempty ((boundedCoherentDerived X).ι.obj L ≅
      (DerivedCategory.singleFunctor X.Modules q).obj B) := by
  have h1 := (ObjectProperty.tStructure_isGE_iff (boundedCoherentDerived X)
    DerivedCategory.TStructure.t L q).mp hGE
  have h2 := (ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived X)
    DerivedCategory.TStructure.t L q).mp hLE
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L.obj q
  exact ⟨B, (show ObjectProperty X.Modules from fun M => M.IsCoherent).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules q).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules q).app B) (L.property.2 q),
    ⟨e⟩⟩

end AlgebraicGeometry

end
