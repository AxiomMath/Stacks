module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# Morphisms of Deligne systems

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `(K_n)`, `(L_m)` be Deligne
systems, with values `K` and `L` on `U`: the restricted systems `(K_n|_U)` and `(L_m|_U)` are
identified with the constant systems at `K` and `L`. A morphism of pro-systems `ξ : (K_n) ⟶ (L_m)`
has, for every `m`, a component in `colim_n Hom_X(K_n, L_m)`, represented by some `g : K_n ⟶ L_m`;
its *restriction to `U`* is the morphism `K ≅ K_n|_U ⟶ L_m|_U ≅ L`, which does not depend on the
choices. This file proves [Stacks, Tag 0G4L] (1) and (3): every `α : K ⟶ L` is the restriction of
a unique morphism of pro-systems, and consequently a Deligne system is determined by its value up
to unique isomorphism of pro-objects. Part (2), the existence of a Deligne system with a
prescribed value, is `AlgebraicGeometry.DeligneSystem.exists_restrictIso`.

By Stacks 0G2X, a morphism of pro-systems `(K_n) ⟶ (L_m)` is a
transformation `colim_m Hom_X(L_m, -) ⟶ colim_n Hom_X(K_n, -)` of their functors of points; by
Stacks 0G2H (`AlgebraicGeometry.DeligneSystem.restrictionLifting`) these functors are
`Hom_U(L, (-)|_U)` and `Hom_U(K, (-)|_U)`; and a transformation of functors of points is
determined by its values on the classes of the identities of the `L_m`.

## Main definitions

* `CategoryTheory.ProSeq.ofHomEquivSeqHomColim`: morphisms of pro-objects of inverse sequences as
  transformations of their functors of points `colim_n Mor(F_n, -)`.
* `AlgebraicGeometry.DeligneSystem.proHomComponent`: the `m`-th component
  `ξ_m ∈ colim_n Hom_X(K_n, L_m)` of a morphism of pro-systems.
* `AlgebraicGeometry.DeligneSystem.restrictProHom`: the restriction to `U` of a morphism of
  pro-systems between Deligne systems.

## Main results

* `AlgebraicGeometry.DeligneSystem.restrictProHom_eq`: the restriction is
  `K ≅ K_n|_U ⟶ L_m|_U ≅ L` for every representative `g : K_n ⟶ L_m` of every component.
* `AlgebraicGeometry.DeligneSystem.restrictProHom_bijective`: restriction is a bijection.
* `AlgebraicGeometry.DeligneSystem.existsUnique_proHom_restrict`: **[Stacks, Tag 0G4L] (1).**
* `AlgebraicGeometry.DeligneSystem.existsUnique_proIso_restrict`: **[Stacks, Tag 0G4L] (3).**

## References

* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe v u u'

namespace CategoryTheory

namespace ProSeq

variable {𝒟 : Type u'} [Category.{v} 𝒟]

/-- **Stacks 0G2X**, with the colimits over the index category of the sequences themselves: a
morphism `ProSeq.of F ⟶ ProSeq.of G` of pro-objects is a transformation
`colim_m Mor(G_m, -) ⟶ colim_n Mor(F_n, -)` of their functors of points. -/
public def ofHomEquivSeqHomColim (F G : ℕᵒᵖ ⥤ 𝒟) :
    (of F ⟶ of G) ≃ (Pro.seqHomColim G ⟶ Pro.seqHomColim F) :=
  (opEquiv _ _).trans (InducedCategory.homEquiv.trans
    ((Pro.seqHomColimIso G).homCongr (Pro.seqHomColimIso F)))

/-- The identity of a pro-object is the identity transformation of its functor of points. -/
public lemma ofHomEquivSeqHomColim_id (F : ℕᵒᵖ ⥤ 𝒟) :
    ofHomEquivSeqHomColim F F (𝟙 (of F)) = 𝟙 _ := by
  show (Pro.seqHomColimIso F).inv ≫ 𝟙 _ ≫ (Pro.seqHomColimIso F).hom = 𝟙 _
  simp

/-- Composition of morphisms of pro-objects is composition of the transformations of functors of
points, in the opposite order. -/
public lemma ofHomEquivSeqHomColim_comp {F G H : ℕᵒᵖ ⥤ 𝒟} (ξ : of F ⟶ of G) (ζ : of G ⟶ of H) :
    ofHomEquivSeqHomColim F H (ξ ≫ ζ) =
      ofHomEquivSeqHomColim G H ζ ≫ ofHomEquivSeqHomColim F G ξ :=
  Iso.homCongr_comp (Pro.seqHomColimIso H) (Pro.seqHomColimIso G) (Pro.seqHomColimIso F)
    ζ.unop.hom ξ.unop.hom

end ProSeq

namespace Pro

variable {𝒟 : Type u'} [Category.{v} 𝒟]

/-- A transformation of functors of points of inverse sequences is determined by its values on
the classes of the identities `id_{G_m}`. -/
public lemma seqHomColim_hom_ext {F G : ℕᵒᵖ ⥤ 𝒟} {η η' : seqHomColim G ⟶ seqHomColim F}
    (h : ∀ m : ℕ, η.app _ (seqStage G (𝟙 (G.obj (op m)))) =
      η'.app _ (seqStage G (𝟙 (G.obj (op m))))) : η = η' := by
  refine NatTrans.ext (funext fun N => ConcreteCategory.hom_ext _ _ fun x => ?_)
  obtain ⟨m, f, rfl⟩ := seqStage_surjective G N x
  obtain ⟨n, g, hg⟩ := seqStage_surjective F _ (η.app _ (seqStage G (𝟙 (G.obj (op m)))))
  rw [transformation_seqStage η g hg f, transformation_seqStage η' g ((h m).symm.trans hg) f]

end Pro

end CategoryTheory

namespace AlgebraicGeometry

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

namespace DeligneSystem

/-- **Stacks 0G2H as an isomorphism of functors**, for any value: if the restriction of a Deligne
system `(K_n)` to `U` is identified by `e` with the constant system at `K`, then
`colim_n Hom_X(K_n, -) ≅ Hom_U(K, (-)|_U)`, the class of `g : K_n ⟶ N` going to
`K ≅ K_n|_U ⟶ N|_U`. -/
public def homIsoOfRestrictIso (D : DeligneSystem j) {K : DerivedCategory U.Modules}
    (e : D.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj K) :
    Pro.seqHomColim D.system ≅ restrictBoundedCoherent j ⋙ coyoneda.obj (op K) :=
  restrictHomIso D.system (restrictBoundedCoherent j) K e D.restrictionLifting

/-- The identification `AlgebraicGeometry.DeligneSystem.homIsoOfRestrictIso` sends the class of
`g : K_n ⟶ N` to `K ≅ K_n|_U ⟶ N|_U`. -/
public lemma homIsoOfRestrictIso_hom_app_seqStage (D : DeligneSystem j)
    {K : DerivedCategory U.Modules}
    (e : D.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj K)
    {N : BoundedCoherentDerived X} {n : ℕ} (g : D.system.obj (op n) ⟶ N) :
    (D.homIsoOfRestrictIso e).hom.app N (Pro.seqStage D.system g) =
      e.inv.app (op n) ≫ (restrictBoundedCoherent j).map g := by
  show (proHomComparison D.system (restrictBoundedCoherent j)
    (coneOfNatIso e ⟨K, 𝟙 _⟩)).app N (Pro.seqStage D.system g) = _
  rw [proHomComparison_stage]
  simp [coneOfNatIso]

variable {D E : DeligneSystem j}

/-- The **`m`-th component** of a morphism of pro-systems `ξ : (K_n) ⟶ (L_m)`: the element
`ξ_m ∈ colim_n Hom_X(K_n, L_m)` that the transformation of functors of points underlying `ξ`
(Stacks 0G2X) attaches to the class of the identity of `L_m`. -/
public def proHomComponent (ξ : D.proObject ⟶ E.proObject) (m : ℕ) :
    (Pro.seqHomColim D.system).obj (E.system.obj (op m)) :=
  (ProSeq.ofHomEquivSeqHomColim D.system E.system ξ).app _
    (Pro.seqStage E.system (𝟙 (E.system.obj (op m))))

variable {K L : DerivedCategory U.Modules}
  (eD : D.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj K)
  (eE : E.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj L)

/-- The **restriction to `U`** of a morphism of pro-systems `ξ : (K_n) ⟶ (L_m)` between Deligne
systems with values `K` and `L`: the morphism `K ≅ K_n|_U ⟶ L_0|_U ≅ L` read off from the
component of `ξ` at `L_0`. By `AlgebraicGeometry.DeligneSystem.restrictProHom_eq` it is the same
morphism `K ≅ K_n|_U ⟶ L_m|_U ≅ L` for every representative `g : K_n ⟶ L_m` of every
component. -/
public def restrictProHom (ξ : D.proObject ⟶ E.proObject) : K ⟶ L :=
  (D.homIsoOfRestrictIso eD).hom.app _ (proHomComponent ξ 0) ≫ eE.hom.app (op 0)

/-- **The restriction is computed by any representative of any component.** If the `m`-th
component of `ξ` is the class of `g : K_n ⟶ L_m`, then the restriction of `ξ` to `U` is
`K ≅ K_n|_U ⟶ L_m|_U ≅ L`. -/
public lemma restrictProHom_eq (ξ : D.proObject ⟶ E.proObject) {m n : ℕ}
    (g : D.system.obj (op n) ⟶ E.system.obj (op m))
    (hg : proHomComponent ξ m = Pro.seqStage D.system g) :
    restrictProHom eD eE ξ =
      eD.inv.app (op n) ≫ (restrictBoundedCoherent j).map g ≫ eE.hom.app (op m) := by
  let t := InverseSequence.tr E.system (Nat.zero_le m)
  have h0 : proHomComponent ξ 0 = Pro.seqStage D.system (g ≫ t) := by
    have hs : Pro.seqStage E.system (𝟙 (E.system.obj (op 0))) = Pro.seqStage E.system t := by
      rw [← Pro.seqStage_transition E.system (Nat.zero_le m), Category.comp_id]
    unfold proHomComponent
    rw [hs]
    exact Pro.transformation_seqStage _ g hg t
  have ht : (restrictBoundedCoherent j).map t ≫ eE.hom.app (op 0) = eE.hom.app (op m) := by
    have := eE.hom.naturality (homOfLE (Nat.zero_le m)).op
    simp only [Functor.comp_map, Functor.const_obj_map] at this
    exact this.trans (Category.comp_id _)
  rw [restrictProHom, h0, homIsoOfRestrictIso_hom_app_seqStage, Functor.map_comp,
    Category.assoc, Category.assoc, ht]

/-- The restriction of `ξ` to `U` is `α` exactly when, for every representative `g : K_n ⟶ L_m`
of every component of `ξ`, the morphism `K ≅ K_n|_U ⟶ L_m|_U` is `K ⟶ L ≅ L_m|_U`. -/
public lemma restrictProHom_eq_iff (ξ : D.proObject ⟶ E.proObject) (α : K ⟶ L) :
    restrictProHom eD eE ξ = α ↔
      ∀ (m n : ℕ) (g : D.system.obj (op n) ⟶ E.system.obj (op m)),
        proHomComponent ξ m = Pro.seqStage D.system g →
          eD.inv.app (op n) ≫ (restrictBoundedCoherent j).map g = α ≫ eE.inv.app (op m) := by
  constructor
  · rintro rfl m n g hg
    rw [restrictProHom_eq eD eE ξ g hg]
    simp
  · intro h
    obtain ⟨n, g, hg⟩ := Pro.seqStage_surjective D.system _ (proHomComponent ξ 0)
    rw [restrictProHom_eq eD eE ξ g hg, ← Category.assoc, h 0 n g hg]
    simp

/-- **Restriction to `U` is injective on morphisms of pro-systems**: a morphism of pro-systems
between Deligne systems is determined by its restriction. Each component `ξ_m` is determined by
its image `K ⟶ L_m|_U` under the bijection of Stacks 0G2H, which is the restriction of `ξ`
followed by `L ≅ L_m|_U`; and the components determine `ξ` (Stacks 0G2X). -/
public lemma restrictProHom_injective : Function.Injective (restrictProHom eD eE) := by
  intro ξ ξ' h
  apply (ProSeq.ofHomEquivSeqHomColim D.system E.system).injective
  refine Pro.seqHomColim_hom_ext fun m => ?_
  apply ((D.homIsoOfRestrictIso eD).app (E.system.obj (op m))).toEquiv.injective
  have key : ∀ ζ : D.proObject ⟶ E.proObject,
      (D.homIsoOfRestrictIso eD).hom.app _ (proHomComponent ζ m) =
        restrictProHom eD eE ζ ≫ eE.inv.app (op m) := fun ζ => by
    obtain ⟨n, g, hg⟩ := Pro.seqStage_surjective D.system _ (proHomComponent ζ m)
    rw [hg, homIsoOfRestrictIso_hom_app_seqStage,
      (restrictProHom_eq_iff eD eE ζ _).mp rfl m n g hg]
  exact (key ξ).trans (h ▸ (key ξ').symm)

/-- The morphism of pro-systems attached to `α : K ⟶ L`, as a transformation of functors of
points: `colim_m Hom_X(L_m, -) ≅ Hom_U(L, (-)|_U) ⟶ Hom_U(K, (-)|_U) ≅ colim_n Hom_X(K_n, -)`,
the middle map being precomposition with `α`. -/
public def proHomOfRestrict (α : K ⟶ L) : D.proObject ⟶ E.proObject :=
  (ProSeq.ofHomEquivSeqHomColim D.system E.system).symm
    ((E.homIsoOfRestrictIso eE).hom ≫
      Functor.whiskerLeft (restrictBoundedCoherent j) (coyoneda.map α.op) ≫
        (D.homIsoOfRestrictIso eD).inv)

/-- The morphism of pro-systems attached to `α` restricts to `α`. -/
public lemma restrictProHom_proHomOfRestrict (α : K ⟶ L) :
    restrictProHom eD eE (proHomOfRestrict eD eE α) = α := by
  have h : proHomComponent (proHomOfRestrict eD eE α) 0 =
      (D.homIsoOfRestrictIso eD).inv.app _ (α ≫ eE.inv.app (op 0) ≫
        (restrictBoundedCoherent j).map (𝟙 _)) := by
    unfold proHomComponent proHomOfRestrict
    rw [Equiv.apply_symm_apply]
    simp only [NatTrans.comp_app, types_comp_apply, Functor.whiskerLeft_app]
    rw [homIsoOfRestrictIso_hom_app_seqStage]
    rfl
  rw [restrictProHom, h]
  simp

/-- **Restriction to `U` is a bijection** from morphisms of pro-systems `(K_n) ⟶ (L_m)` between
Deligne systems to morphisms `K ⟶ L` between their values. -/
public lemma restrictProHom_bijective : Function.Bijective (restrictProHom eD eE) :=
  ⟨restrictProHom_injective eD eE, fun α => ⟨proHomOfRestrict eD eE α,
    restrictProHom_proHomOfRestrict eD eE α⟩⟩

/-- **Stacks Project, Tag 0G4L (1).** Let `j : U ⟶ X` be an open immersion of Noetherian schemes,
let `(K_n)` and `(L_m)` be Deligne systems and let `K` and `L` be the values of the constant
systems `(K_n|_U)` and `(L_m|_U)`, through the identifications `eD` and `eE`. Given a morphism
`α : K ⟶ L` of `D(𝒪_U)`, there is a unique morphism of pro-systems `ξ : (K_n) ⟶ (L_m)` of
`D^b_{Coh}(𝒪_X)` whose restriction to `U` is `α`: for every `m`, and every representative
`g : K_n ⟶ L_m` of the `m`-th component of `ξ` in `colim_n Hom_X(K_n, L_m)`, the restriction
`K ≅ K_n|_U ⟶ L_m|_U` of `g` is `K ⟶ L ≅ L_m|_U`.

Morphisms of pro-systems are transformations of the functors they corepresent (Stacks 0G2X),
which by Stacks 0G2H are `Hom_U(L, (-)|_U)` and `Hom_U(K, (-)|_U)`. -/
@[stacks 0G4L "(1)"]
public theorem existsUnique_proHom_restrict (α : K ⟶ L) :
    ∃! ξ : D.proObject ⟶ E.proObject,
      ∀ (m n : ℕ) (g : D.system.obj (op n) ⟶ E.system.obj (op m)),
        proHomComponent ξ m = Pro.seqStage D.system g →
          eD.inv.app (op n) ≫ (restrictBoundedCoherent j).map g = α ≫ eE.inv.app (op m) := by
  refine ⟨proHomOfRestrict eD eE α,
    (restrictProHom_eq_iff eD eE _ α).mp (restrictProHom_proHomOfRestrict eD eE α),
    fun ξ hξ => restrictProHom_injective eD eE ?_⟩
  rw [(restrictProHom_eq_iff eD eE ξ α).mpr hξ, restrictProHom_proHomOfRestrict]

/-- The identity of a Deligne system restricts to the identity of its value. -/
public lemma restrictProHom_id : restrictProHom eD eD (𝟙 D.proObject) = 𝟙 K := by
  have h : proHomComponent (𝟙 D.proObject) 0 =
      Pro.seqStage D.system (𝟙 (D.system.obj (op 0))) := by
    unfold proHomComponent
    rw [ProSeq.ofHomEquivSeqHomColim_id]
    rfl
  rw [restrictProHom_eq eD eD _ _ h]
  simp

variable {F : DeligneSystem j} {M : DerivedCategory U.Modules}
  (eF : F.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj M)

/-- Restriction to `U` is compatible with composition of morphisms of pro-systems. -/
public lemma restrictProHom_comp (ξ : D.proObject ⟶ E.proObject)
    (ζ : E.proObject ⟶ F.proObject) :
    restrictProHom eD eF (ξ ≫ ζ) = restrictProHom eD eE ξ ≫ restrictProHom eE eF ζ := by
  obtain ⟨n, g, hg⟩ := Pro.seqStage_surjective E.system _ (proHomComponent ζ 0)
  obtain ⟨k, h, hh⟩ := Pro.seqStage_surjective D.system _ (proHomComponent ξ n)
  have hc : proHomComponent (ξ ≫ ζ) 0 = Pro.seqStage D.system (h ≫ g) := by
    unfold proHomComponent
    rw [ProSeq.ofHomEquivSeqHomColim_comp]
    show (ProSeq.ofHomEquivSeqHomColim D.system E.system ξ).app _
      (proHomComponent ζ 0) = _
    rw [hg]
    exact Pro.transformation_seqStage _ h hh g
  rw [restrictProHom_eq eD eF _ _ hc, restrictProHom_eq eD eE _ _ hh,
    restrictProHom_eq eE eF _ _ hg, Functor.map_comp]
  simp

/-- **Stacks Project, Tag 0G4L (3).** Let `j : U ⟶ X` be an open immersion of Noetherian schemes.
The pro-object of a Deligne system with value `K` (part (2)) is unique up to unique isomorphism
as a pro-object: for Deligne systems `(K_n)` and `(K'_n)` whose restrictions to `U` are
identified, by `eD` and `eE`, with the constant system at `K`, there is a unique isomorphism of
pro-objects `(K_n) ≅ (K'_n)` whose restriction to `U` is the identity of `K`: for every `m`, and
every representative `g : K_n ⟶ K'_m` of the `m`-th component of its forward morphism, the
restriction `K ≅ K_n|_U ⟶ K'_m|_U` of `g` is `K ≅ K'_m|_U`.

This follows from part (1): the morphisms restricting to the identity in the two
directions compose to morphisms restricting to the identity, which are the identities. -/
@[stacks 0G4L "(3)"]
public theorem existsUnique_proIso_restrict
    (eD : D.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj K)
    (eE : E.system ⋙ restrictBoundedCoherent j ≅ (Functor.const ℕᵒᵖ).obj K) :
    ∃! i : D.proObject ≅ E.proObject,
      ∀ (m n : ℕ) (g : D.system.obj (op n) ⟶ E.system.obj (op m)),
        proHomComponent i.hom m = Pro.seqStage D.system g →
          eD.inv.app (op n) ≫ (restrictBoundedCoherent j).map g = eE.inv.app (op m) := by
  have key : ∀ i : D.proObject ⟶ E.proObject,
      (∀ (m n : ℕ) (g : D.system.obj (op n) ⟶ E.system.obj (op m)),
        proHomComponent i m = Pro.seqStage D.system g →
          eD.inv.app (op n) ≫ (restrictBoundedCoherent j).map g = eE.inv.app (op m)) ↔
        restrictProHom eD eE i = 𝟙 K := fun i => by
    rw [restrictProHom_eq_iff]
    simp only [Category.id_comp]
  let ξ := proHomOfRestrict eD eE (𝟙 K)
  let ζ := proHomOfRestrict eE eD (𝟙 K)
  have hξ : restrictProHom eD eE ξ = 𝟙 K := restrictProHom_proHomOfRestrict eD eE _
  have hζ : restrictProHom eE eD ζ = 𝟙 K := restrictProHom_proHomOfRestrict eE eD _
  have h₁ : ξ ≫ ζ = 𝟙 _ := restrictProHom_injective eD eD (by
    rw [restrictProHom_comp eD eE eD, hξ, hζ, restrictProHom_id, Category.id_comp])
  have h₂ : ζ ≫ ξ = 𝟙 _ := restrictProHom_injective eE eE (by
    rw [restrictProHom_comp eE eD eE, hξ, hζ, restrictProHom_id, Category.id_comp])
  refine ⟨⟨ξ, ζ, h₁, h₂⟩, (key ξ).mpr hξ, fun i hi => Iso.ext ?_⟩
  exact restrictProHom_injective eD eE (((key i.hom).mp hi).trans hξ.symm)

end DeligneSystem

end AlgebraicGeometry

end
