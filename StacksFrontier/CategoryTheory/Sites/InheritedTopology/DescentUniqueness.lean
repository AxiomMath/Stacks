module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing

/-! # A descent datum determines the object it descends to, up to isomorphism

Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)` whose presheaves `Mor(x, y)` are
sheaves — condition (2) of Stacks 026F. If two objects of the fibre over `U` both descend one
and the same descent datum relative to a covering sieve of `U`, they are isomorphic: the
comparisons of the two families of cartesian morphisms give isomorphisms of the fibres over the
members of the sieve, these are compatible with base change because both families are
compatible with the gluing isomorphisms of the datum, and
`CategoryTheory.Functor.exists_fiberIso_of_locally` glues them.

This is the uniqueness half of the equivalence, provided by conditions (2) and (3) of
Stacks 026F, between the fibre over `U` and the category of descent data relative to a covering
sieve of `U`; effectiveness, condition (3), is its existence half.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.nonempty_iso_of_descends`.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

universe v₁ v₂ u₁ u₂

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} {R : Sieve U}

namespace SieveDescentDatum

/-- The condition, on a family of cartesian morphisms from the objects of a descent datum `D` to
an object `a` of the fibre over `U`, that it be compatible with the gluing isomorphisms of `D`.
Together with cartesianness this is what
`CategoryTheory.Functor.SieveDescentDatum.IsEffective` asserts the existence of. -/
def Descends (D : SieveDescentDatum p R) (a : p.Fiber U)
    (ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1) : Prop :=
  (∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), p.IsCartesian f (ζ f hf)) ∧
    ∀ ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R.arrows f) ⦃g : W ⟶ U⦄ (hg : R.arrows g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ ζ g hg =
        IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ ζ f hf

/-- Effectiveness of a descent datum is exactly the existence of an object of the fibre over `U`
to which it descends. -/
lemma isEffective_iff_exists_descends (D : SieveDescentDatum p R) :
    D.IsEffective ↔ ∃ (a : p.Fiber U)
      (ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1), D.Descends p a ζ :=
  Iff.rfl

variable {p}

/-- The comparison isomorphism, in the fibre over the source of `f`, between the chosen pullback
along `f` of an object `a` to which `D` descends and the object of `D` at `f`: both carry a
cartesian morphism over `f` to `a`. -/
noncomputable def descendsIso {D : SieveDescentDatum p R} {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1}
    (h : D.Descends p a ζ) ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    pullbackFiber p a f ≅ D.obj f hf :=
  fiberIsoOfCartesian f (IsPreFibered.pullbackMap a.2 f) (ζ f hf)
    (IsPreFibered.pullbackMap.IsCartesian _ _) (h.1 f hf)

/-- `CategoryTheory.Functor.SieveDescentDatum.descendsIso` is compatible with the two cartesian
morphisms over `f` that define it: composing its `hom` with the morphism `ζ f hf` of the
descending family gives the chosen cartesian lift of `f` at `a`. -/
@[reassoc (attr := simp)]
lemma descendsIso_hom_fac {D : SieveDescentDatum p R} {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1}
    (h : D.Descends p a ζ) ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    Fiber.fiberInclusion.map (descendsIso h f hf).hom ≫ ζ f hf =
      IsPreFibered.pullbackMap a.2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse form of the factorization: composing the `inv` of
`CategoryTheory.Functor.SieveDescentDatum.descendsIso` with the chosen cartesian lift of `f` at
`a` gives the morphism `ζ f hf` of the descending family. -/
@[reassoc (attr := simp)]
lemma descendsIso_inv_fac {D : SieveDescentDatum p R} {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1}
    (h : D.Descends p a ζ) ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    Fiber.fiberInclusion.map (descendsIso h f hf).inv ≫ IsPreFibered.pullbackMap a.2 f =
      ζ f hf :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- The gluing isomorphism of `D` between a member `f` of the sieve and a member `b` of it that
`γ ≫ f` equals, read as an isomorphism `γ^* (D f) ≅ D b` of the fibre by contracting the chosen
pullback along the identity. -/
noncomputable def isoAlong (D : SieveDescentDatum p R) ⦃V W : 𝒮⦄ {f : V ⟶ U}
    (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b) (hb' : R.arrows b) :
    pullbackFiber p (D.obj f hf) γ ≅ D.obj b hb' :=
  D.iso hf hb' γ (𝟙 W) (by rw [Category.id_comp]; exact hb) ≪≫
    pullbackFiberIdIso (D.obj b hb')

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
/-- The factorization of `CategoryTheory.Functor.SieveDescentDatum.isoAlong` through a family of
cartesian morphisms that `D` descends along: composing it with the morphism at `b` gives the
morphism at `f`, pulled back along `γ`. -/
lemma isoAlong_comp {D : SieveDescentDatum p R} {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1}
    (h : D.Descends p a ζ) ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    Fiber.fiberInclusion.map (D.isoAlong hf γ hb hb').hom ≫ ζ b hb' =
      IsPreFibered.pullbackMap (D.obj f hf).2 γ ≫ ζ f hf := by
  have hcompat := h.2 hf hb' γ (𝟙 W) (by rw [Category.id_comp]; exact hb)
  rw [isoAlong]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, pullbackFiberIdIso_hom_fac]
  exact hcompat

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
/-- **A descent datum determines the object it descends to.** If two objects `a₁`, `a₂` of the
fibre over `U` both descend one and the same descent datum relative to a covering sieve of `U`,
they are isomorphic.

The composites of the two comparison isomorphisms
`CategoryTheory.Functor.SieveDescentDatum.descendsIso` are isomorphisms `f^* a₁ ≅ f^* a₂` over
the members of the sieve; that they are compatible with base change is proved by comparing both
with the gluing isomorphism `CategoryTheory.Functor.SieveDescentDatum.isoAlong`, using
`CategoryTheory.Functor.SieveDescentDatum.isoAlong_comp` for each of the two families; and
`CategoryTheory.Functor.exists_fiberIso_of_locally` then glues them. -/
theorem nonempty_iso_of_descends {J : GrothendieckTopology 𝒮}
    (hmor : ∀ (c d : p.Fiber U), IsMorSheaf p J U c d) (hR : R ∈ J U)
    {D : SieveDescentDatum p R} {a₁ a₂ : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a₁.1}
    {ξ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a₂.1}
    (hζ : D.Descends p a₁ ζ) (hξ : D.Descends p a₂ ξ) :
    Nonempty (a₁ ≅ a₂) := by
  -- The comparison at a member `b` of the sieve that `γ ≫ f` equals factors through the gluing
  -- isomorphism along `γ`: both composites with the cartesian morphism at `b` are the chosen
  -- cartesian lift of `b` at `a₁`.
  have hfactor : ∀ ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
      (hb : γ ≫ f = b) (hb' : R.arrows b),
      descendsIso hζ b hb' = (pullbackFiberCompIso' a₁ f γ b hb).symm ≪≫
        pullbackFiberIso (descendsIso hζ f hf) γ ≪≫ D.isoAlong hf γ hb hb' := by
    intro V W f hf γ b hb hb'
    refine Iso.ext (fiber_hom_ext_of_cartesian b (ζ b hb') (hζ.1 b hb') _ _ ?_)
    simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
      Category.assoc, isoAlong_comp hζ hf γ hb hb', pullbackFiberHom_fac_assoc,
      descendsIso_hom_fac, pullbackFiberCompIso'_inv_fac]
  -- The local comparisons, and their compatibility with base change.
  have hcompat : ∀ ⦃V W : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U)
      (hb : γ ≫ f = b) (hb' : R.arrows b),
      (descendsIso hζ b hb' ≪≫ (descendsIso hξ b hb').symm).hom =
        (pullbackFiberCompIso' a₁ f γ b hb).inv ≫
          pullbackFiberHom (descendsIso hζ f hf ≪≫ (descendsIso hξ f hf).symm).hom γ ≫
          (pullbackFiberCompIso' a₂ f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    refine fiber_hom_ext_of_cartesian b (IsPreFibered.pullbackMap a₂.2 b)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
    rw [hfactor hf γ hb hb']
    simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
      Category.assoc, descendsIso_inv_fac, pullbackFiberCompIso'_hom_fac,
      pullbackFiberHom_fac_assoc, isoAlong_comp hξ hf γ hb hb']
  obtain ⟨e, -⟩ := exists_fiberIso_of_locally p hmor hR
    (fun {_V} f hf => descendsIso hζ f hf ≪≫ (descendsIso hξ f hf).symm) hcompat
  exact ⟨e⟩

end SieveDescentDatum

end Functor

end CategoryTheory
