module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Direct image along an integral morphism, on the small étale site of Stacks 021B

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category whose
morphism of schemes is integral — a finite morphism, for instance.  Part (1) of Stacks 04C2 says
that the small étale direct image along `f` carries surjections of sheaves of sets to
surjections.  That statement is already proved, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact`, but on Mathlib's small
étale site `AlgebraicGeometry.Scheme.Etale` of *all* schemes étale over the base.  This file
transports it to the small étale site of Stacks 021B, `AlgebraicGeometry.SmallEtale B S hS`,
whose objects are cut down to the schemes the big site contains.

The transport runs along the comparison of the two sites, which is already available: the
embedding `AlgebraicGeometry.SmallEtale.toEtaleSite` that forgets the size cutoff is a dense
subsite inclusion, `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, so restriction of
sheaves along it is an equivalence.  What the transport needs on top of that, and what is proved
here, is that the comparison is compatible with *base change*: the square

```
SmallEtale B S ---- base change along f ----> SmallEtale B T
      |                                            |
 toEtaleSite                                   toEtaleSite
      v                                            v
   S.Etale  ------ base change along f ------->  T.Etale
```

commutes up to a canonical natural isomorphism.  It does so because both base changes are fibre
products — one taken in the size-bounded category of schemes, one in all schemes — and the
inclusion of the former into the latter preserves fibre products (Stacks 021D).

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`: the natural isomorphism filling the
  square above.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms` is
  **Stacks 04C2, part (1), on the small étale site of Stacks 021B**: for `f` with integral
  underlying morphism of schemes, the direct image of sheaves of sets along bounded small étale
  base change carries surjections to surjections.

## Implementation notes

**The direction in which the square is stated is not arbitrary.**  It is stated with the bounded
base change first, so that its components are morphisms *into* `pullback (B.inclusion.map X.hom)
(B.inclusion.map f)`, an honest chosen fibre product in `Scheme` to which
`CategoryTheory.Limits.pullback.hom_ext` applies directly.  Stated the other way round the
components land in the image of a fibre product under the inclusion, and the two projections are
only available after composing with the comparison morphism.

**Why the proof is a chain of `rw` steps and not `simp`.**  `AlgebraicGeometry.Scheme.Etale` is
`CategoryTheory.MorphismProperty.Over` at the property `AlgebraicGeometry.Etale`, which is a
function used at the type `CategoryTheory.MorphismProperty Scheme`; the two are definitionally
equal but not syntactically, and a `simp`, `rw` or `dsimp` whose matching has to pass through
that coercion fails with an application type mismatch under `implicit` transparency.  The proof
therefore (i) reduces everything to the underlying morphisms of schemes with the four
`rfl`-lemmas `comp_left_etale`, `toEtaleSite_map_left`, `smallEtaleBaseChange_pushforwardMap` and
`toEtaleSiteBaseChange_map_left`, and only then (ii) computes, by `rw`, entirely inside `Scheme`
and the bounded category of schemes, where no morphism property occurs.  No compiler option is
relaxed anywhere.

**Universes.**  The objects of both sites live in `Type (u + 1)`, so that is the universe of the
sheaves of sets in which the comparison is instantiated.  Part (1) of Stacks 04C2 is stated for
an arbitrary coefficient universe, so no universe hypothesis is incurred.

## References

* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-! ### Reducing to the underlying morphisms of schemes -/

/-- Composition in Mathlib's small étale site is composition of the underlying morphisms of
schemes.  Stated so that it can be rewritten with: see the implementation notes. -/
theorem comp_left_etale {A C D : T.obj.Etale} (a : A ⟶ C) (b : C ⟶ D) :
    (a ≫ b).left = a.left ≫ b.left := rfl

/-- Composition in the underlying category of a big étale site is composition of the underlying
morphisms of schemes. -/
theorem comp_hom_scheme {A C D : B.Scheme} (a : A ⟶ C) (b : C ⟶ D) :
    (a ≫ b).hom = a.hom ≫ b.hom := rfl

/-- The structure triangle of a morphism of objects of the small étale category, read on
underlying schemes. -/
theorem w_inclusion {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    B.inclusion.map k.hom.left ≫ B.inclusion.map Y.obj.hom = B.inclusion.map X.obj.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (CategoryTheory.Over.w k.hom))

/-- Bounded small étale base change of a morphism, read on underlying schemes: it is the
canonical morphism of chosen fibre products in the size-bounded category of schemes. -/
noncomputable abbrev boundedBaseChangeMap {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    pullback X.obj.hom f ⟶ pullback Y.obj.hom f :=
  pullback.lift (pullback.fst X.obj.hom f ≫ k.hom.left) (pullback.snd X.obj.hom f)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.fst X.obj.hom f ≫ z)
        (CategoryTheory.Over.w k.hom)).trans pullback.condition))

/-- Unbounded small étale base change of a morphism of charts, read on underlying schemes: the
canonical morphism of chosen fibre products in all schemes. -/
noncomputable abbrev unboundedBaseChangeMap {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    pullback (B.inclusion.map X.obj.hom) (B.inclusion.map f) ⟶
      pullback (B.inclusion.map Y.obj.hom) (B.inclusion.map f) :=
  pullback.lift
    (pullback.fst (B.inclusion.map X.obj.hom) (B.inclusion.map f) ≫ B.inclusion.map k.hom.left)
    (pullback.snd (B.inclusion.map X.obj.hom) (B.inclusion.map f))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.fst (B.inclusion.map X.obj.hom) (B.inclusion.map f) ≫ z)
        (w_inclusion B k)).trans pullback.condition))

/-- Base change in the bounded site, followed by the embedding, acts on underlying schemes by
`AlgebraicGeometry.SmallEtale.boundedBaseChangeMap`. -/
theorem toEtaleSiteBaseChange_map_left {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    (((AlgebraicGeometry.smallEtaleBaseChange B f) ⋙
        toEtaleSite B T.obj T.property).map k).left =
      B.inclusion.map (boundedBaseChangeMap B f k) := rfl

/-- The embedding, followed by base change in Mathlib's site, acts on underlying schemes by
`AlgebraicGeometry.SmallEtale.unboundedBaseChangeMap`. -/
theorem toEtaleSite_map_left {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    ((toEtaleSite B S.obj S.property ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).map k).left =
      unboundedBaseChangeMap B f k := rfl

/-! ### The comparison of the two base changes -/

/-- The component of the comparison at an object of the bounded small étale site: the chosen
fibre product of the size-bounded category, pushed into all schemes, is the chosen fibre product
there, because the inclusion preserves fibre products (Stacks 021D). -/
noncomputable def toEtaleSiteBaseChangeComponent (X : SmallEtale B S.obj S.property) :
    ((AlgebraicGeometry.smallEtaleBaseChange B f) ⋙ toEtaleSite B T.obj T.property).obj X ≅
      (toEtaleSite B S.obj S.property ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).obj X :=
  MorphismProperty.Over.isoMk (PreservesPullback.iso B.inclusion X.obj.hom f)
    (PreservesPullback.iso_hom_snd B.inclusion X.obj.hom f)

/-- On underlying schemes, the comparison component is the canonical isomorphism between the
image of the bounded fibre product and the fibre product of the images. -/
theorem toEtaleSiteBaseChangeComponent_hom_left (X : SmallEtale B S.obj S.property) :
    (toEtaleSiteBaseChangeComponent B f X).hom.left =
      (PreservesPullback.iso B.inclusion X.obj.hom f).hom := rfl

/-- The first projection of the naturality square of the comparison. -/
theorem toEtaleSiteBaseChange_naturality_fst {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    (B.inclusion.map (boundedBaseChangeMap B f k) ≫
        (PreservesPullback.iso B.inclusion Y.obj.hom f).hom) ≫
      pullback.fst (B.inclusion.map Y.obj.hom) (B.inclusion.map f) =
    ((PreservesPullback.iso B.inclusion X.obj.hom f).hom ≫ unboundedBaseChangeMap B f k) ≫
      pullback.fst (B.inclusion.map Y.obj.hom) (B.inclusion.map f) := by
  rw [Category.assoc, PreservesPullback.iso_hom_fst, ← B.inclusion.map_comp,
    boundedBaseChangeMap, pullback.lift_fst, Category.assoc, unboundedBaseChangeMap,
    pullback.lift_fst, ← Category.assoc, PreservesPullback.iso_hom_fst, ← B.inclusion.map_comp]

/-- The second projection of the naturality square of the comparison. -/
theorem toEtaleSiteBaseChange_naturality_snd {X Y : SmallEtale B S.obj S.property} (k : X ⟶ Y) :
    (B.inclusion.map (boundedBaseChangeMap B f k) ≫
        (PreservesPullback.iso B.inclusion Y.obj.hom f).hom) ≫
      pullback.snd (B.inclusion.map Y.obj.hom) (B.inclusion.map f) =
    ((PreservesPullback.iso B.inclusion X.obj.hom f).hom ≫ unboundedBaseChangeMap B f k) ≫
      pullback.snd (B.inclusion.map Y.obj.hom) (B.inclusion.map f) := by
  rw [Category.assoc, PreservesPullback.iso_hom_snd, ← B.inclusion.map_comp,
    boundedBaseChangeMap, pullback.lift_snd, Category.assoc, unboundedBaseChangeMap,
    pullback.lift_snd, PreservesPullback.iso_hom_snd]

/-- **The comparison of the two small étale sites is compatible with base change.** For a
morphism `f : T ⟶ S` of the underlying category of a big étale site, base change in the small
étale site of Stacks 021B followed by the embedding into Mathlib's small étale site is the
embedding followed by base change there.

Both composites send an object to a chosen fibre product, one formed in the size-bounded category
of schemes and then pushed into all schemes, the other formed in all schemes; the inclusion of
the bounded category preserves fibre products by Stacks 021D, which is the comparison, and its
naturality is the two projection identities
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChange_naturality_fst` and
`…_snd`. -/
noncomputable def toEtaleSiteBaseChangeIso :
    (AlgebraicGeometry.smallEtaleBaseChange B f) ⋙ toEtaleSite B T.obj T.property ≅
      toEtaleSite B S.obj S.property ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f) :=
  NatIso.ofComponents (toEtaleSiteBaseChangeComponent B f) fun k => by
    apply MorphismProperty.Over.Hom.ext
    rw [comp_left_etale, comp_left_etale, toEtaleSiteBaseChangeComponent_hom_left,
      toEtaleSiteBaseChangeComponent_hom_left, toEtaleSiteBaseChange_map_left,
      toEtaleSite_map_left]
    exact pullback.hom_ext (toEtaleSiteBaseChange_naturality_fst B f k)
      (toEtaleSiteBaseChange_naturality_snd B f k)

/-! ### Stacks 04C2, part (1), on the small étale site of Stacks 021B -/

/-- A composite of two functors preserving epimorphisms preserves epimorphisms.  Stated with
the two hypotheses as explicit arguments, since neither is found by instance search at the
concrete functors below. -/
theorem preservesEpimorphisms_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : F.PreservesEpimorphisms) (hG : G.PreservesEpimorphisms) :
    (F ⋙ G).PreservesEpimorphisms where
  preserves {_ _} φ _ := by
    have : Epi (F.map φ) := hF.preserves φ
    exact hG.preserves (F.map φ)

/-- **Stacks 04C2, part (1), on the small étale site of Stacks 021B.** Let `f : T ⟶ S` be a
morphism of the underlying category of a big étale site whose morphism of schemes is integral — a
finite morphism, for instance.  Then the direct image of sheaves of sets along bounded small
étale base change along `f` carries surjections to surjections.

Part (1) of Stacks 04C2 on Mathlib's small étale site is
`Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom`, and
restriction along `AlgebraicGeometry.SmallEtale.toEtaleSite` is an equivalence of sheaf
categories because the embedding is a dense subsite inclusion.  Transporting the first along
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso` therefore exhibits
`toEtaleSite_* ⋙ (bounded base change)_*` as a composite carrying surjections to surjections,
and the equivalence `toEtaleSite_*` on its left cancels. -/
theorem smallEtaleBaseChange_pushforward_preservesEpimorphisms
    [IsIntegralHom (B.inclusion.map f)] :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (topology B S.obj S.property) (topology B T.obj T.property)).PreservesEpimorphisms := by
  have hc : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  have hc1 : (toEtaleSite B S.obj S.property ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ S.obj.smallEtaleTopology _
  have hc2 : (AlgebraicGeometry.smallEtaleBaseChange B f ⋙
      toEtaleSite B T.obj T.property).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B T.obj T.property) _
  -- the comparison of direct images, from the comparison of base changes
  have hiso :
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
            (Type (u + 1)) S.obj.smallEtaleTopology T.obj.smallEtaleTopology ⋙
          (toEtaleSite B S.obj S.property).sheafPushforwardContinuous (Type (u + 1))
            (topology B S.obj S.property) S.obj.smallEtaleTopology ≅
        (toEtaleSite B T.obj T.property).sheafPushforwardContinuous (Type (u + 1))
            (topology B T.obj T.property) T.obj.smallEtaleTopology ⋙
          (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (topology B S.obj S.property) (topology B T.obj T.property) :=
    Functor.sheafPushforwardContinuousComp' (F := toEtaleSite B S.obj S.property)
        (G := Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
        (Iso.refl _) _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousIso (toEtaleSiteBaseChangeIso B f).symm _ _ _ ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (F := AlgebraicGeometry.smallEtaleBaseChange B f)
          (G := toEtaleSite B T.obj T.property) (Iso.refl _) _ _ _ _).symm
  have hlhs := preservesEpimorphisms_comp
    ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
      (Type (u + 1)) S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
    ((toEtaleSite B S.obj S.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B S.obj S.property) S.obj.smallEtaleTopology)
    (Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom
      (B.inclusion.map f))
    inferInstance
  let e := ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous (Type (u + 1))
    (topology B T.obj T.property) T.obj.smallEtaleTopology).asEquivalence
  have hcancel := preservesEpimorphisms_comp e.inverse
    (e.functor ⋙ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (Type (u + 1)) (topology B S.obj S.property) (topology B T.obj T.property))
    inferInstance (Functor.PreservesEpimorphisms.of_iso hiso)
  exact Functor.PreservesEpimorphisms.of_iso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso _ ≪≫ Functor.leftUnitor _)

end AlgebraicGeometry.SmallEtale

end
