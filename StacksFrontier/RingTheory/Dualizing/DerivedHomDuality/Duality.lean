module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived Hom into a dualizing complex is a duality

Let `A` be a Noetherian ring and `ω` a dualizing complex for `A`. Derived Hom into `ω` is the
contravariant functor `D : K ↦ RHom_A(K, ω)` on the derived category of `A`-modules. This file
assembles the duality statements of [stacks 0A7C] from the two halves already available: the
exchange of cohomological bounds of `Dualizing.dualizingDerivedHom_isLE_of_isGE` and
`Dualizing.dualizingDerivedHom_isGE_of_isLE`, and canonical biduality
`Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`.

The biduality morphisms are first packaged as a natural transformation
`𝟭 ⟶ opOp ⋙ D.op ⋙ D` on the whole derived category. Naturality is proved at the level of an
arbitrary derived tensor--Hom adjunction: the biduality morphism is the transpose of evaluation
after tensor symmetry, so naturality follows from naturality of the transpose in its source,
dinaturality in the internal-Hom variable, naturality of tensor symmetry, and dinaturality of
evaluation — four of the structure fields of
`StacksDraft.DerivedHom.DerivedHomAdjunction` and nothing else.

Restricting to objects with finite cohomology, canonical biduality becomes a natural
isomorphism, and that alone makes `D` an anti-equivalence: a functor `F : Cᵒᵖ ⥤ C` equipped with
a natural isomorphism `𝟭 C ≅ opOp C ⋙ F.op ⋙ F` is fully faithful and essentially surjective,
with no further input. The same argument applies verbatim on the bounded subcategory, since
derived Hom into `ω` preserves cohomological boundedness.

The exchange of boundedness below and above is the bound exchange in one direction and the
bound exchange composed with biduality in the other: if `RHom_A(K, ω)` is bounded above then
`RHom_A(RHom_A(K, ω), ω)` is bounded below, and biduality identifies that with `K`.

## Main definitions

* `Dualizing.derivedBiduality` — the canonical biduality morphisms as a natural transformation
  on the whole derived category.
* `Dualizing.CoherentDerivedCategory`, `Dualizing.BoundedCoherentDerivedCategory` — the full
  subcategories of objects with finite cohomology, and of bounded such objects.
* `Dualizing.coherentDualizingDerivedHomFunctor`,
  `Dualizing.boundedCoherentDualizingDerivedHomFunctor` — the restrictions of `RHom_A(-, ω)`.
* `Dualizing.coherentDerivedBiduality`, `Dualizing.coherentDerivedBidualityIso` — canonical
  biduality on objects with finite cohomology.

## Main results

* `Dualizing.isEquivalence_of_opOpNatIso` — a functor `Cᵒᵖ ⥤ C` whose square is naturally
  isomorphic to the identity is an equivalence.
* `Dualizing.dualizingDerivedHom_biduality_isIso` — canonical biduality is a natural
  isomorphism on objects with finite cohomology.
* `Dualizing.coherentDualizingDerivedHom_isEquivalence` and
  `Dualizing.boundedCoherentDualizingDerivedHom_isEquivalence` — the two anti-equivalences.
* `Dualizing.dualizingDerivedHom_plus_iff_minus` and
  `Dualizing.dualizingDerivedHom_minus_iff_plus` — the two exchanges of boundedness.

## Implementation notes

The derived category of `A`-modules is taken at the standard model, as in
`StacksFrontier/RingTheory/Dualizing/DualizingDerivedHom.lean`: the model is baked into the type of
`Dualizing.dualizingDerivedHomFunctor`, so it is forced here rather than chosen. No statement in
this file mentions coproducts, and the standard model is a legitimate derived category of
`ModuleCat A`, so nothing is weakened by the pin.

No `@[stacks 0A7C]` attribute is placed here. The decomposition of that tag has ten
declarations, nine of which are now available; the tenth, the Ext–cohomology comparison, is
missing, and the audit scanner keys on the bare four-character tag, so an attribute here would
render the whole tag formalized.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Dualizing

open StacksDraft.DerivedHom

/-! ### A contravariant functor whose square is the identity is an equivalence -/

section OpOp

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- A functor `F : Cᵒᵖ ⥤ C` with a natural isomorphism `𝟭 C ≅ opOp C ⋙ F.op ⋙ F` is faithful:
the naturality square identifies a morphism with its image under `F` applied twice. -/
theorem faithful_of_opOpNatIso (F : Cᵒᵖ ⥤ C)
    (η : Functor.id C ≅ opOp C ⋙ F.op ⋙ F) : F.Faithful where
  map_injective {X X'} f g hfg := by
    have h2 : f.unop ≫ η.hom.app X.unop = η.hom.app X'.unop ≫ F.map (F.map f).op :=
      η.hom.naturality f.unop
    have h3 : g.unop ≫ η.hom.app X.unop = η.hom.app X'.unop ≫ F.map (F.map g).op :=
      η.hom.naturality g.unop
    rw [hfg, ← h3] at h2
    exact Quiver.Hom.unop_inj ((cancel_mono (η.hom.app X.unop)).1 h2)

/-- A functor `F : Cᵒᵖ ⥤ C` with a natural isomorphism `𝟭 C ≅ opOp C ⋙ F.op ⋙ F` is essentially
surjective: every object is the image of the opposite of its `F`-image. -/
theorem essSurj_of_opOpNatIso (F : Cᵒᵖ ⥤ C)
    (η : Functor.id C ≅ opOp C ⋙ F.op ⋙ F) : F.EssSurj where
  mem_essImage Y := ⟨Opposite.op (F.obj (Opposite.op Y)), ⟨(η.app Y).symm⟩⟩

/-- A functor `F : Cᵒᵖ ⥤ C` with a natural isomorphism `𝟭 C ≅ opOp C ⋙ F.op ⋙ F` is full: the
transpose of a morphism through the two components of `η` is a preimage, by naturality of `η`
and faithfulness of `F`. -/
theorem full_of_opOpNatIso (F : Cᵒᵖ ⥤ C)
    (η : Functor.id C ≅ opOp C ⋙ F.op ⋙ F) : F.Full where
  map_surjective {X X'} g := by
    have := faithful_of_opOpNatIso F η
    refine ⟨(η.hom.app X'.unop ≫ F.map g.op ≫ η.inv.app X.unop).op, ?_⟩
    have h2 : (η.hom.app X'.unop ≫ F.map g.op ≫ η.inv.app X.unop) ≫ η.hom.app X.unop =
        η.hom.app X'.unop ≫
          F.map (F.map (η.hom.app X'.unop ≫ F.map g.op ≫ η.inv.app X.unop).op).op :=
      η.hom.naturality _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app] at h2
    simp only [Functor.comp_obj, Functor.op_obj, Functor.id_obj, opOp_obj, Opposite.unop_op,
      Opposite.op_unop, Category.comp_id] at h2
    exact (Quiver.Hom.op_inj (F.map_injective ((cancel_epi (η.hom.app X'.unop)).1 h2))).symm

/-- **A contravariant functor whose square is naturally isomorphic to the identity is an
equivalence.** This is the only categorical input to the two anti-equivalences of
[stacks 0A7C]: once canonical biduality is a natural isomorphism, derived Hom into a dualizing
complex is an anti-equivalence for formal reasons. -/
theorem isEquivalence_of_opOpNatIso (F : Cᵒᵖ ⥤ C)
    (η : Functor.id C ≅ opOp C ⋙ F.op ⋙ F) : F.IsEquivalence :=
  ⟨faithful_of_opOpNatIso F η, full_of_opOpNatIso F η, essSurj_of_opOpNatIso F η⟩

end OpOp

/-! ### Naturality of the biduality morphism -/

section AbstractNaturality

universe u₁ v₁ w₁

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : DerivedHomAdjunction R)

/-- **The canonical biduality morphism is natural.** For an arbitrary derived tensor--Hom
adjunction, the transpose of evaluation after tensor symmetry is natural in its argument. The
proof uses only four structure fields: naturality of the transpose in its source, dinaturality
of the transpose in the internal-Hom variable, naturality of tensor symmetry, and dinaturality
of evaluation. -/
theorem bidualityMor_naturality (ω : DerivedCategory (ModuleCat.{v₁} R))
    {K K' : DerivedCategory (ModuleCat.{v₁} R)} (f : K ⟶ K') :
    f ≫ bidualityMor d ω K' =
      bidualityMor d ω K ≫
        d.hom.map (((d.hom.map ((f.op, 𝟙 ω) :
          (Opposite.op K', ω) ⟶ (Opposite.op K, ω))).op, 𝟙 ω) :
          (Opposite.op (d.hom.obj (Opposite.op K, ω)), ω) ⟶
            (Opposite.op (d.hom.obj (Opposite.op K', ω)), ω)) := by
  apply (d.homEquiv K (d.hom.obj (Opposite.op K', ω)) ω).injective
  rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality]
  simp only [bidualityMor, AddEquiv.apply_symm_apply]
  rw [d.tensorSwap_naturality_assoc, d.tensorSwap_naturality_assoc,
    d.evaluation_naturality_left]

end AbstractNaturality

/-! ### Biduality as a natural transformation -/

section Duality

universe u v

attribute [local instance 5000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **The canonical biduality morphisms, natural in the derived object.** Each component is the
canonical morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` of
`Dualizing.dualizingBidualityMor`; naturality is `Dualizing.bidualityMor_naturality` at the
adjunction of [stacks 0A63]. -/
@[stacks 0A7C "canonical biduality morphism"]
def derivedBiduality (ω : DerivedCategory (ModuleCat.{max u v} A)) :
    Functor.id (DerivedCategory (ModuleCat.{max u v} A)) ⟶
      opOp (DerivedCategory (ModuleCat.{max u v} A)) ⋙
        (dualizingDerivedHomFunctor.{u, v} A ω).op ⋙
          dualizingDerivedHomFunctor.{u, v} A ω where
  app K := dualizingBidualityMor.{u, v} A ω K
  naturality {_K _K'} f := bidualityMor_naturality _ ω f

/-- The derived category of `A`-modules with finite cohomology in every degree. -/
abbrev CoherentDerivedCategory :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory (ModuleCat.{max u v} A) => ∀ i : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))

/-- The bounded derived category of `A`-modules with finite cohomology. -/
abbrev BoundedCoherentDerivedCategory :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory (ModuleCat.{max u v} A) =>
      (∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) ∧
      (DerivedCategory.TStructure.t).bounded K)

variable [IsNoetherianRing A]

/-- The restriction of `RHom_A(-, ω)` to objects with finite cohomology. It lands in that
subcategory by `Dualizing.dualizingDerivedHom_finiteCohomology`. -/
def coherentDualizingDerivedHomFunctor
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    (CoherentDerivedCategory.{u, v} A)ᵒᵖ ⥤ CoherentDerivedCategory.{u, v} A where
  obj K := ⟨(dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K.unop.obj),
    dualizingDerivedHom_finiteCohomology.{u, v} A ω hω K.unop.obj K.unop.property⟩
  map f := ⟨(dualizingDerivedHomFunctor.{u, v} A ω).map ((ObjectProperty.ι _).map f.unop).op⟩
  map_id X := by
    ext
    dsimp
    exact (dualizingDerivedHomFunctor.{u, v} A ω).map_id _
  map_comp f g := by
    ext
    dsimp
    exact (dualizingDerivedHomFunctor.{u, v} A ω).map_comp _ _

/-- The restriction of canonical biduality to objects with finite cohomology. -/
def coherentDerivedBiduality
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    Functor.id (CoherentDerivedCategory.{u, v} A) ⟶
      opOp (CoherentDerivedCategory.{u, v} A) ⋙
        (coherentDualizingDerivedHomFunctor.{u, v} A ω hω).op ⋙
          coherentDualizingDerivedHomFunctor.{u, v} A ω hω where
  app K := ⟨(derivedBiduality.{u, v} A ω).app K.obj⟩
  naturality {_K _L} f := by
    ext
    exact (derivedBiduality.{u, v} A ω).naturality f.hom

/-- A morphism of a full subcategory is invertible as soon as the underlying morphism is. -/
private theorem isIso_homMk_of_isIso {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) (h : IsIso f) : IsIso (ObjectProperty.homMk f) :=
  ⟨⟨ObjectProperty.homMk (inv f), by ext; simp, by ext; simp⟩⟩

/-- **Canonical biduality is a natural isomorphism on objects with finite cohomology.** Each
component is invertible by `Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`, and a
morphism of a full subcategory is invertible as soon as the underlying morphism is. -/
@[stacks 0A7C "canonical biduality"]
theorem dualizingDerivedHom_biduality_isIso
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    IsIso (coherentDerivedBiduality.{u, v} A ω hω) := by
  have happ (K) : IsIso ((coherentDerivedBiduality.{u, v} A ω hω).app K) := by
    have := isIso_dualizingBidualityMor_of_finiteCohomology.{u, v} A ω K.obj hω K.property
    exact isIso_homMk_of_isIso _ this
  exact NatIso.isIso_of_isIso_app _

/-- The canonical natural isomorphism from the identity functor to double derived duality on
objects with finite cohomology. -/
def coherentDerivedBidualityIso
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    Functor.id (CoherentDerivedCategory.{u, v} A) ≅
      opOp (CoherentDerivedCategory.{u, v} A) ⋙
        (coherentDualizingDerivedHomFunctor.{u, v} A ω hω).op ⋙
          coherentDualizingDerivedHomFunctor.{u, v} A ω hω :=
  have := dualizingDerivedHom_biduality_isIso.{u, v} A ω hω
  asIso (coherentDerivedBiduality.{u, v} A ω hω)

/-- **Derived Hom into a dualizing complex is an anti-equivalence on the derived category of
objects with finite cohomology, [stacks 0A7C].** -/
@[stacks 0A7C "the anti-equivalence on coherent objects", sga "5 I App.7.3" "affine case"]
theorem coherentDualizingDerivedHom_isEquivalence
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    (coherentDualizingDerivedHomFunctor.{u, v} A ω hω).IsEquivalence :=
  isEquivalence_of_opOpNatIso _ (coherentDerivedBidualityIso.{u, v} A ω hω)

/-! ### Exchange of boundedness -/

/-- **On objects with finite cohomology, derived Hom into a dualizing complex exchanges bounded
below with bounded above.** The forward implication is the bound exchange
`Dualizing.dualizingDerivedHom_isLE_of_isGE`; the converse applies the other bound exchange to
`RHom_A(K, ω)` and transports the resulting bound along canonical biduality. -/
@[stacks 0A7C "exchange of bounded below and bounded above"]
theorem dualizingDerivedHom_plus_iff_minus
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    (DerivedCategory.TStructure.t).plus K ↔
      (DerivedCategory.TStructure.t).minus
        ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K)) := by
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  refine ⟨fun ⟨n, hn⟩ => ⟨b - n, dualizingDerivedHom_isLE_of_isGE.{u, v} A ω K n a b hn hamp⟩,
    fun ⟨m, hm⟩ => ⟨a - m, ?_⟩⟩
  have hbid : IsIso (dualizingBidualityMor.{u, v} A ω K) :=
    isIso_dualizingBidualityMor_of_finiteCohomology.{u, v} A ω K hω hK
  have := dualizingDerivedHom_isGE_of_isLE.{u, v} A ω
    ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K)) m a b hm hamp
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (asIso (dualizingBidualityMor.{u, v} A ω K)).symm (a - m)

/-- **On objects with finite cohomology, derived Hom into a dualizing complex exchanges bounded
above with bounded below.** The forward implication is the bound exchange
`Dualizing.dualizingDerivedHom_isGE_of_isLE`; the converse applies the other bound exchange to
`RHom_A(K, ω)` and transports the resulting bound along canonical biduality. -/
@[stacks 0A7C "exchange of bounded above and bounded below"]
theorem dualizingDerivedHom_minus_iff_plus
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    (DerivedCategory.TStructure.t).minus K ↔
      (DerivedCategory.TStructure.t).plus
        ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K)) := by
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  refine ⟨fun ⟨n, hn⟩ => ⟨a - n, dualizingDerivedHom_isGE_of_isLE.{u, v} A ω K n a b hn hamp⟩,
    fun ⟨m, hm⟩ => ⟨b - m, ?_⟩⟩
  have hbid : IsIso (dualizingBidualityMor.{u, v} A ω K) :=
    isIso_dualizingBidualityMor_of_finiteCohomology.{u, v} A ω K hω hK
  have := dualizingDerivedHom_isLE_of_isGE.{u, v} A ω
    ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K)) m a b hm hamp
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (dualizingBidualityMor.{u, v} A ω K)).symm (b - m)

/-! ### The bounded anti-equivalence -/

/-- The restriction of `RHom_A(-, ω)` to bounded objects with finite cohomology. It lands in
that subcategory by `Dualizing.dualizingDerivedHom_finiteCohomology` and
`Dualizing.dualizingDerivedHom_bounded`. -/
def boundedCoherentDualizingDerivedHomFunctor
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    (BoundedCoherentDerivedCategory.{u, v} A)ᵒᵖ ⥤ BoundedCoherentDerivedCategory.{u, v} A where
  obj K := ⟨(dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K.unop.obj),
    dualizingDerivedHom_finiteCohomology.{u, v} A ω hω K.unop.obj K.unop.property.1,
    dualizingDerivedHom_bounded.{u, v} A ω hω K.unop.obj K.unop.property.1
      K.unop.property.2⟩
  map f := ⟨(dualizingDerivedHomFunctor.{u, v} A ω).map ((ObjectProperty.ι _).map f.unop).op⟩
  map_id X := by
    ext
    dsimp
    exact (dualizingDerivedHomFunctor.{u, v} A ω).map_id _
  map_comp f g := by
    ext
    dsimp
    exact (dualizingDerivedHomFunctor.{u, v} A ω).map_comp _ _

/-- The restriction of canonical biduality to bounded objects with finite cohomology. -/
def boundedCoherentDerivedBiduality
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    Functor.id (BoundedCoherentDerivedCategory.{u, v} A) ⟶
      opOp (BoundedCoherentDerivedCategory.{u, v} A) ⋙
        (boundedCoherentDualizingDerivedHomFunctor.{u, v} A ω hω).op ⋙
          boundedCoherentDualizingDerivedHomFunctor.{u, v} A ω hω where
  app K := ⟨(derivedBiduality.{u, v} A ω).app K.obj⟩
  naturality {_K _L} f := by
    ext
    exact (derivedBiduality.{u, v} A ω).naturality f.hom

/-- Canonical biduality is a natural isomorphism on bounded objects with finite cohomology. -/
theorem boundedCoherentDerivedBiduality_isIso
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    IsIso (boundedCoherentDerivedBiduality.{u, v} A ω hω) := by
  have happ (K) : IsIso ((boundedCoherentDerivedBiduality.{u, v} A ω hω).app K) := by
    have := isIso_dualizingBidualityMor_of_finiteCohomology.{u, v} A ω K.obj hω K.property.1
    exact isIso_homMk_of_isIso _ this
  exact NatIso.isIso_of_isIso_app _

/-- The canonical natural isomorphism from the identity functor to double derived duality on
bounded objects with finite cohomology. -/
def boundedCoherentDerivedBidualityIso
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    Functor.id (BoundedCoherentDerivedCategory.{u, v} A) ≅
      opOp (BoundedCoherentDerivedCategory.{u, v} A) ⋙
        (boundedCoherentDualizingDerivedHomFunctor.{u, v} A ω hω).op ⋙
          boundedCoherentDualizingDerivedHomFunctor.{u, v} A ω hω :=
  have := boundedCoherentDerivedBiduality_isIso.{u, v} A ω hω
  asIso (boundedCoherentDerivedBiduality.{u, v} A ω hω)

/-- **Derived Hom into a dualizing complex is an anti-equivalence on bounded objects with finite
cohomology, [stacks 0A7C].** -/
@[stacks 0A7C "the bounded anti-equivalence", sga "5 I App.7.3" "affine case"]
theorem boundedCoherentDualizingDerivedHom_isEquivalence
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    (boundedCoherentDualizingDerivedHomFunctor.{u, v} A ω hω).IsEquivalence :=
  isEquivalence_of_opOpNatIso _ (boundedCoherentDerivedBidualityIso.{u, v} A ω hω)

end Duality

end Dualizing

end
