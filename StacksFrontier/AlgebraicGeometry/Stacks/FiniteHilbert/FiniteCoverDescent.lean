module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverIsom
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverRefinement
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DescentUniqueness
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.SieveDescentDatumPairCocone

/-!
# Descent data for the category of finite locally free covers are effective

Let `S` be a scheme contained in a big fppf site `B` and let `d` be a natural number. This file
proves the third of the three conditions of Stacks 05WB for the category `ℋ_d` of degree-`d`
finite locally free covers of `AlgebraicGeometry.Stack.finiteCoverCategory`: every descent datum
for `ℋ_d` relative to a covering family of the big fppf site, with genuine fibre-product double
and triple overlaps and indexed by an arbitrary type, is effective.

The source calls this the hardest part of 05WB, and all of its geometry is already in hand: a
diagram of covers over an fpqc covering family descends, which is
`AlgebraicGeometry.Stack.FiniteCover.exists_descended_of_diagram`. What remains is bookkeeping,
and it is organised by the source's own first move, "in order to prove effectivity we may first
refine the covering":

* `CategoryTheory.Functor.DescentDatum.isEffective_of_refinements` reduces the condition for a
  covering *family* indexed by an arbitrary type to the condition for descent data relative to
  *one* covering refinement of each covering sieve, granted condition (2) of Stacks 026F — here
  `AlgebraicGeometry.Stack.isMorSheaf_finiteCoverProjection`, which does not consume effective
  descent, so the reduction is not circular;
* `AlgebraicGeometry.BigFppfOver.exists_fpqc_family_refining` supplies the refinement, a covering
  family whose underlying morphisms of schemes form an fpqc covering family;
* the objects a descent datum attaches to that family, together with the objects it attaches to
  the chosen fibre products of its members and of triples of them, form exactly the diagram that
  `AlgebraicGeometry.Stack.FiniteCover.exists_descended_of_diagram` descends.

## Main results

* `AlgebraicGeometry.Stack.descentDatum_isEffective_finiteCoverProjection`: **condition (3) of
  Stacks 05WB for `ℋ_d`**, the `effective_descent` field of
  `CategoryTheory.Functor.IsStackInGroupoids` for
  `AlgebraicGeometry.Stack.finiteCoverProjection`.

## Implementation notes

The descended cover is produced as a bare scheme, so it has to be put back into the site: a
finite locally free morphism is finite and locally of finite presentation, hence of finite type,
and the size cutoff of a big fppf site is closed under the source of a finite type morphism,
Stacks 000R (5). That is
`AlgebraicGeometry.Stack.contains_source_of_isFiniteLocallyFreeOfRank` below, and lifting the
whole cocone back along the inclusion is `exists_site_cover_of_scheme_cocone`: the inclusion of
the site into schemes is fully faithful and reflects fibre products, so the cartesian squares and
the gluing identities descend with it.

Effectivity relative to a covering sieve asks for a cartesian morphism out of the object attached
to *every* arrow of the sieve, not only out of the objects attached to the members of the refining
family. The missing morphisms are obtained from a chosen factorization of the arrow through a
member of the family, by the transport `datumMap` of the datum along that factorization — the
contraction `CategoryTheory.Functor.SieveDescentDatum.contract` of the datum onto the object at
the composite, inverted, followed by the chosen cartesian lift. Independence of the choice is not
an extra argument: the compatibility
`CategoryTheory.Functor.SieveDescentDatum.descends_of_isoAlong` asks for is a condition in a
single variable, and it follows from the gluing identity of the descended cover over the chosen
fibre products together with the composition law `datumMap_comp`, which is the cocycle condition
of the datum.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w v u₁ v₁ u₂ v₂

namespace AlgebraicGeometry.Stack

/-! ### A descent datum transported along an arrow of its sieve -/

section SieveTransport

open CategoryTheory.Functor

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {p : E ⥤ C} [p.IsFibered] {U : C} {R : Sieve U}

/-- The morphism between the objects a sieve-indexed descent datum attaches to two arrows of its
sieve, one of which factors through the other: contract the chosen pullback of the object at the
longer arrow onto the object at the shorter one, and follow the chosen cartesian lift. -/
private def datumMap (D : SieveDescentDatum p R)
    {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : (D.obj g hg).1 ⟶ (D.obj f hf).1 :=
  CategoryTheory.Functor.SieveDescentDatum.transportMap D hf hg a ha

/-- The transport `datumMap` of a descent datum along a factorization lies cartesianly over that
factorization. -/
private lemma datumMap_cartesian (D : SieveDescentDatum p R)
    {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : p.IsCartesian a (datumMap D hf hg a ha) := by
  have : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map (D.contract hf a hg ha).inv) :=
    (D.contract hf a hg ha).inv.2
  have : p.IsCartesian a (IsPreFibered.pullbackMap (D.obj f hf).2 a) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have hh : p.IsCartesian (𝟙 W ≫ a) (datumMap D hf hg a ha) := by
    dsimp [datumMap, CategoryTheory.Functor.SieveDescentDatum.transportMap]
    infer_instance
  simpa using hh

/-- The transport of a descent datum absorbs a contraction of the datum into a gluing
isomorphism: this is the cocycle condition read at a triple whose third arrow is an identity. -/
private lemma datumMap_glue (D : SieveDescentDatum p R)
    {V W Z : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : Z ⟶ V) (a' : Z ⟶ W)
    (ha : a ≫ f = b) (ha' : a' ≫ g = b) :
    Fiber.fiberInclusion.map (D.contract hf a hb ha).hom ≫ datumMap D hg hb a' ha' =
      Fiber.fiberInclusion.map (D.iso hf hg a a' (ha.trans ha'.symm)).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 a' := by
  have h : (D.contract hf a hb ha).hom ≫ (D.contract hg a' hb ha').inv =
      (D.iso hf hg a a' (ha.trans ha'.symm)).hom := by
    rw [Iso.comp_inv_eq]
    simp only [SieveDescentDatum.contract, Iso.trans_hom, ← Category.assoc]
    rw [D.cocycle hf hg hb a a' (𝟙 Z)]
  simp only [datumMap, CategoryTheory.Functor.SieveDescentDatum.transportMap, ← Category.assoc,
    ← Functor.map_comp, h]

/-- The transport of a descent datum is functorial in the factorization. -/
private lemma datumMap_comp (D : SieveDescentDatum p R)
    {V W Z : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : W ⟶ V) (a' : Z ⟶ W)
    (ha : a ≫ f = g) (ha' : a' ≫ g = b) :
    datumMap D hg hb a' ha' ≫ datumMap D hf hg a ha =
      datumMap D hf hb (a' ≫ a) (by rw [Category.assoc, ha, ha']) := by
  have he : pullbackFiberIso (D.contract hf a hg ha) a' ≪≫ D.contract hg a' hb ha' =
      pullbackFiberCompIso (D.obj f hf) a a' ≪≫
        D.contract hf (a' ≫ a) hb (by rw [Category.assoc, ha, ha']) := by
    apply Iso.ext
    simp only [Iso.trans_hom, pullbackFiberIso_hom]
    rw [D.pullbackFiberHom_contract]
    simp only [SieveDescentDatum.contract, Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (D.iso hf hg (a' ≫ a) a' _).hom, D.cocycle]
  have hi := congrArg Iso.inv he
  simp only [Iso.trans_inv, pullbackFiberIso_inv] at hi
  simp only [datumMap, CategoryTheory.Functor.SieveDescentDatum.transportMap, Category.assoc]
  rw [← pullbackFiberHom_fac_assoc, ← Category.assoc, ← Functor.map_comp, hi,
    Functor.map_comp, Category.assoc, pullbackFiberCompIso_inv_fac]

end SieveTransport

/-! ### Putting the descended cover back into the site -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- **The source of a finite locally free morphism over an object of a big fppf site is again an
object of that site.** A finite locally free morphism is finite and locally of finite
presentation, hence of finite type, and the size cutoff of a big fppf site is closed under the
source of a finite type morphism, Stacks 000R (5). -/
private theorem contains_source_of_isFiniteLocallyFreeOfRank (B : BigFppfSite.{u})
    {T Z : Scheme.{u}} (q : Z ⟶ T) (r : ℕ) (hT : B.Contains T)
    (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r) : B.Contains Z := by
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r := hq
  have hproperties :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree q r)
  let : IsFinite q := hproperties.1
  let : QuasiCompact q := inferInstance
  let : LocallyOfFinitePresentation q := hproperties.2.2
  let : LocallyOfFiniteType q := inferInstance
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q hT

/-- **A cocone of schemes over a finite locally free morphism lifts to the site.** Given a family
`{pr l : W l ⟶ V l}` of morphisms of the big fppf category over `S`, a family `{f l : V l ⟶ U}`
and a finite locally free morphism `q` of rank `r` of schemes over `U` presenting every `W l` as
the base change of `q` along `f l`, the morphism `q` is the image of a morphism of the site, and
the whole cocone lifts: the inclusion of the site into schemes is fully faithful and reflects
fibre products. -/
private lemma exists_site_cover_of_scheme_cocone
    {U : BigFppfOver B S hS} {L : Type v} {V W : L → BigFppfOver B S hS}
    (f : ∀ l, V l ⟶ U) (pr : ∀ l, W l ⟶ V l)
    {Z : Scheme.{u}} (q : Z ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (r : ℕ) (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r)
    (g : ∀ l, (BigFppfOver.toScheme B S hS).obj (W l) ⟶ Z)
    (sq : ∀ l, IsPullback (g l) ((BigFppfOver.toScheme B S hS).map (pr l)) q
      ((BigFppfOver.toScheme B S hS).map (f l))) :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U) (g' : ∀ l, W l ⟶ Z'),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map q') r ∧
      (∀ l, IsPullback (g' l) (pr l) q' (f l)) ∧
      ∀ {A : BigFppfOver B S hS} (l m : L) (a : A ⟶ W l) (b : A ⟶ W m),
        (BigFppfOver.toScheme B S hS).map a ≫ g l =
          (BigFppfOver.toScheme B S hS).map b ≫ g m →
        a ≫ g' l = b ≫ g' m := by
  classical
  let H := BigFppfOver.toScheme B S hS
  have hz : B.Contains Z :=
    contains_source_of_isFiniteLocallyFreeOfRank B q r U.left.property hq
  let q₀ : B.obj hz ⟶ U.left := B.inclusion.preimage q
  let Z' : BigFppfOver B S hS := Over.mk (q₀ ≫ U.hom)
  let q' : Z' ⟶ U := Over.homMk q₀
  let g₀ (l : L) : (W l).left ⟶ B.obj hz := B.inclusion.preimage (g l)
  have hq₀ : B.inclusion.map q₀ = q :=
    B.inclusion.map_preimage (X := B.obj hz) (Y := U.left) q
  have hg₀map (l : L) : B.inclusion.map (g₀ l) = g l :=
    B.inclusion.map_preimage (X := (W l).left) (Y := B.obj hz) (g l)
  have hg₀ (l : L) : g₀ l ≫ q₀ = (pr l).left ≫ (f l).left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_comp, hq₀, hg₀map]
    exact (sq l).w
  let g' (l : L) : W l ⟶ Z' := Over.homMk (g₀ l) (by
    show g₀ l ≫ (q₀ ≫ U.hom) = (W l).hom
    rw [← Category.assoc, hg₀, Category.assoc, Over.w, Over.w])
  have hq' : H.map q' = q := hq₀
  have hg' (l : L) : H.map (g' l) = g l := hg₀map l
  refine ⟨Z', q', g', ?_, ?_, ?_⟩
  · show Stacks.Morphisms.IsFiniteLocallyFreeOfRank (H.map q') r
    rw [hq']
    exact hq
  · intro l
    apply IsPullback.of_map_of_faithful H
    simpa only [hq', hg'] using sq l
  · intro A l m a b hab
    apply H.map_injective
    simpa only [Functor.map_comp, hg'] using hab

end Site

/-! ### The descended cover of a descent datum over an fpqc covering family -/

section Descent

open CategoryTheory.Functor

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.Fiber.mk finiteCoverProjection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- The projection from `ℋ_d` to the site is a fibered category. -/
local instance isFibered_finiteCoverProjection :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
  Functor.IsFiberedInGroupoids.isFibered
    (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))

/-- The base object of the cover a descent datum for `ℋ_d` attaches to an arrow of its sieve is
the source of that arrow. This is the second component of the object of the fibre, spelled with
the field of the cover rather than with the projection, so that the identifications appearing in
the statements below are literally the same term. -/
private lemma obj_U {U : BigFppfOver B S hS} {R : Sieve U}
    (D : SieveDescentDatum
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) R)
    {X : BigFppfOver B S hS} (f : X ⟶ U) (hf : R f) : (D.obj f hf).1.U = X :=
  (D.obj f hf).2

/-- The base component of the transport of a descent datum for `ℋ_d` along a factorization is
that factorization, read through the identifications of the base objects. -/
private lemma datumMap_f {U : BigFppfOver B S hS} {R : Sieve U}
    (D : SieveDescentDatum
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) R)
    {X Y : BigFppfOver B S hS} {f : X ⟶ U} (hf : R f) {g : Y ⟶ U} (hg : R g)
    (a : Y ⟶ X) (ha : a ≫ f = g) :
    (datumMap D hf hg a ha).f =
      eqToHom (obj_U D g hg) ≫ a ≫ eqToHom (obj_U D f hf).symm := by
  have := (datumMap_cartesian D hf hg a ha).toIsHomLift
  exact IsHomLift.fac'
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) a (datumMap D hf hg a ha)

/-- A morphism out of the object a descent datum for `ℋ_d` attaches to an arrow of its sieve, formed
by transporting along a factorization and then following a morphism over a member of the family,
lies over the arrow. -/
private lemma isHomLift_datumMap_comp {U : BigFppfOver B S hS} {R : Sieve U}
    (D : SieveDescentDatum
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) R)
    {X Y : BigFppfOver B S hS} {f : X ⟶ U} (hf : R f) {b : Y ⟶ U} (hb : R b)
    (a : Y ⟶ X) (ha : a ≫ f = b) {cv : FiniteCover B S hS d} (ζ : (D.obj f hf).1 ⟶ cv)
    (hζ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift f ζ) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift b
      (datumMap D hf hb a ha ≫ ζ) := by
  have := (datumMap_cartesian D hf hb a ha).toIsHomLift
  have h : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
      (a ≫ f) (datumMap D hf hb a ha ≫ ζ) := inferInstance
  rwa [ha] at h

/-- Two morphisms of `ℋ_d` lying over one and the same morphism of the site and agreeing in their
cover component are equal: the base component of a morphism is determined by the morphism it lies
over. -/
private lemma hom_ext_of_isHomLift {P Q : FiniteCover B S hS d}
    {X Y : BigFppfOver B S hS} (m : X ⟶ Y) (φ ψ : P ⟶ Q)
    (hφ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift m φ)
    (hψ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift m ψ)
    (hg : φ.g = ψ.g) : φ = ψ := by
  refine FiniteCover.Hom.ext ?_ hg
  have := hφ
  have := hψ
  exact (IsHomLift.fac'
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) m φ).trans
    (IsHomLift.fac'
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) m ψ).symm

/-- A cartesian square one of whose legs is the composite of a morphism with an identification of
objects, read with that identification moved to the opposite leg. -/
private lemma isPullback_of_comp_eqToHom {C : Type u₁} [Category.{v₁} C]
    {P X Y Y' T : C} (fst : P ⟶ X) (snd : P ⟶ Y') (g₁ : X ⟶ T) (g₂ : Y ⟶ T) (e : Y' = Y)
    (h : IsPullback fst (snd ≫ eqToHom e) g₁ g₂) :
    IsPullback fst snd g₁ (eqToHom e ≫ g₂) := by
  cases e
  simpa using h

/-- A cartesian square conjugated by identifications of its three non-terminal corners. -/
private lemma isPullback_eqToHom_conj {C : Type u₁} [Category.{v₁} C]
    {P X Y T P' X' Y' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {g₁ : X ⟶ T} {g₂ : Y ⟶ T}
    (h : IsPullback fst snd g₁ g₂) (eP : P' = P) (eX : X' = X) (eY : Y' = Y) :
    IsPullback (eqToHom eP ≫ fst ≫ eqToHom eX.symm) (eqToHom eP ≫ snd ≫ eqToHom eY.symm)
      (eqToHom eX ≫ g₁) (eqToHom eY ≫ g₂) := by
  cases eP
  cases eX
  cases eY
  simpa using h

/-- The identification of the base object of a cover with an object of the site, moved from the
structure morphism of the cover to the morphism of the site, on underlying schemes. -/
private lemma isPullback_map_eqToHom_of_cover {U : BigFppfOver B S hS} {Z₀ : Scheme.{u}}
    (q₀ : Z₀ ⟶ (BigFppfOver.toScheme B S hS).obj U) (W : BigFppfOver B S hS)
    (P : FiniteCover B S hS d) (eW : P.U = W) (fW : W ⟶ U)
    (G : (BigFppfOver.toScheme B S hS).obj P.Z ⟶ Z₀)
    (h : IsPullback G ((BigFppfOver.toScheme B S hS).map P.q) q₀
      ((BigFppfOver.toScheme B S hS).map (eqToHom eW ≫ fW))) :
    IsPullback G ((BigFppfOver.toScheme B S hS).map (P.q ≫ eqToHom eW)) q₀
      ((BigFppfOver.toScheme B S hS).map fW) := by
  cases eW
  simpa using h

/-- **A morphism of `ℋ_d` lies over its base component**, read through an identification of its
source base object with an object of the site. -/
private lemma isHomLift_of_f_eq {P Q : FiniteCover B S hS d} {A : BigFppfOver B S hS}
    (φ : P ⟶ Q) (eP : P.U = A) (m : A ⟶ Q.U) (h : φ.f = eqToHom eP ≫ m) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift m φ := by
  cases eP
  have hm : m = φ.f := by simpa using h.symm
  cases hm
  exact CategoryTheory.IsHomLift.map _ φ

/-- **The cover a descent datum for `ℋ_d` descends to over an fpqc covering family.** The objects
the datum attaches to the members of the family, to the chosen fibre products of pairs of them and
to the chosen fibre products of triples of them form a diagram of degree-`d` finite locally free
covers over a covering family that is fpqc on underlying schemes, so
`AlgebraicGeometry.Stack.FiniteCover.exists_descended_of_diagram` descends it; the descended
scheme is put back into the site by `exists_site_cover_of_scheme_cocone`.

The last clause is the gluing identity in the form the verification of effectivity consumes it:
two factorizations of one and the same arrow of the sieve through two members of the family give
one and the same morphism to the descended cover. -/
private lemma exists_descended_cover_of_fpqc_family {U : BigFppfOver B S hS} {R : Sieve U}
    (D : SieveDescentDatum
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) R)
    {L : Type v} {V : L → BigFppfOver B S hS} (f : ∀ l, V l ⟶ U) (hR : ∀ l, R (f l))
    (hfpqc : Presieve.ofArrows (fun l ↦ (BigFppfOver.toScheme B S hS).obj (V l))
      (fun l ↦ (BigFppfOver.toScheme B S hS).map (f l)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ (cv : FiniteCover B S hS d)
      (hcv : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).obj cv = U)
      (ζ : ∀ l, (D.obj (f l) (hR l)).1 ⟶ cv),
      (∀ l, (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
        (f l) (ζ l)) ∧
      ∀ {A : BigFppfOver B S hS} (l m : L) {b : A ⟶ U} (hb : R b)
        (a : A ⟶ V l) (a' : A ⟶ V m) (ha : a ≫ f l = b) (ha' : a' ≫ f m = b),
        datumMap D (hR l) hb a ha ≫ ζ l = datumMap D (hR m) hb a' ha' ≫ ζ m := by
  classical
  let H := BigFppfOver.toScheme B S hS
  let pr₁ (l m : L) := pullback.fst (f l) (f m)
  let pr₂ (l m : L) := pullback.snd (f l) (f m)
  let f₂ (l m : L) := pr₁ l m ≫ f l
  let h₂ (l m : L) := R.downward_closed (hR l) (pr₁ l m)
  let P (l : L) := (D.obj (f l) (hR l)).1
  let Q (l m : L) := (D.obj (f₂ l m) (h₂ l m)).1
  let c (l m : L) := datumMap D (hR l) (h₂ l m) (pr₁ l m) rfl
  let e (l m : L) := datumMap D (hR m) (h₂ l m) (pr₂ l m) pullback.condition.symm
  let fP (l : L) : (P l).U ⟶ U := eqToHom (obj_U D (f l) (hR l)) ≫ f l
  have hfpqc' : Presieve.ofArrows (fun l ↦ H.obj (P l).U) (fun l ↦ H.map (fP l)) ∈
      Scheme.fpqcPrecoverage (H.obj U) := by
    have he {X Y : L → BigFppfOver B S hS} (h : ∀ l, X l = Y l) (a : ∀ l, Y l ⟶ U) :
        Presieve.ofArrows (fun l ↦ H.obj (X l)) (fun l ↦ H.map (eqToHom (h l) ≫ a l)) =
          Presieve.ofArrows (fun l ↦ H.obj (Y l)) (fun l ↦ H.map (a l)) := by
      cases funext h
      simp
    exact (he (fun l ↦ obj_U D (f l) (hR l)) f).symm ▸ hfpqc
  have sq₂ (l m : L) : IsPullback (c l m).f (e l m).f (fP l) (fP m) := by
    dsimp only [c, e]
    rw [datumMap_f, datumMap_f]
    exact isPullback_eqToHom_conj (IsPullback.of_hasPullback (f l) (f m))
      (obj_U D (f₂ l m) (h₂ l m)) (obj_U D (f l) (hR l)) (obj_U D (f m) (hR m))
  let t (l m n : L) := pullback.fst (f₂ l m) (f n)
  let s (l m n : L) := pullback.snd (f₂ l m) (f n)
  let f₃ (l m n : L) := t l m n ≫ f₂ l m
  let h₃ (l m n : L) := R.downward_closed (h₂ l m) (t l m n)
  let T (l m n : L) := (D.obj (f₃ l m n) (h₃ l m n)).1
  let u₂₃ (l m n : L) : pullback (f₂ l m) (f n) ⟶ pullback (f m) (f n) :=
    pullback.lift (t l m n ≫ pr₂ l m) (s l m n) (by
      rw [Category.assoc, ← pullback.condition]
      exact pullback.condition)
  let u₁₃ (l m n : L) : pullback (f₂ l m) (f n) ⟶ pullback (f l) (f n) :=
    pullback.lift (t l m n ≫ pr₁ l m) (s l m n) (by
      rw [Category.assoc]; exact pullback.condition)
  have hu₂₃ (l m n : L) : u₂₃ l m n ≫ f₂ m n = f₃ l m n := by
    dsimp only [u₂₃, f₂, f₃, pr₁, pr₂]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, ← pullback.condition]
  have hu₁₃ (l m n : L) : u₁₃ l m n ≫ f₂ l n = f₃ l m n := by
    dsimp only [u₁₃, f₂, f₃, pr₁]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  let b₁₂ (l m n : L) := datumMap D (h₂ l m) (h₃ l m n) (t l m n) rfl
  let b₂₃ (l m n : L) := datumMap D (h₂ m n) (h₃ l m n) (u₂₃ l m n) (hu₂₃ l m n)
  let b₁₃ (l m n : L) := datumMap D (h₂ l n) (h₃ l m n) (u₁₃ l m n) (hu₁₃ l m n)
  have hc₁ (l m n : L) : b₁₂ l m n ≫ c l m = b₁₃ l m n ≫ c l n := by
    dsimp only [b₁₂, b₁₃, c]
    rw [datumMap_comp, datumMap_comp]
    simp only [u₁₃, pr₁, pullback.lift_fst]
  have hc₂ (l m n : L) : b₁₂ l m n ≫ e l m = b₂₃ l m n ≫ c m n := by
    dsimp only [b₁₂, b₂₃, c, e]
    rw [datumMap_comp, datumMap_comp]
    simp only [u₂₃, pr₁, pullback.lift_fst]
  have hc₃ (l m n : L) : b₂₃ l m n ≫ e m n = b₁₃ l m n ≫ e l n := by
    dsimp only [b₂₃, b₁₃, e]
    rw [datumMap_comp, datumMap_comp]
    simp only [u₂₃, u₁₃, pr₂, pullback.lift_snd]
  have sq₃ (l m n : L) : IsPullback (b₁₂ l m n).f (b₂₃ l m n ≫ e m n).f
      ((c l m).f ≫ fP l) (fP n) := by
    have hleg : (c l m).f ≫ fP l = eqToHom (obj_U D (f₂ l m) (h₂ l m)) ≫ f₂ l m := by
      dsimp only [c, fP, f₂]
      rw [datumMap_f]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hleg]
    dsimp only [b₁₂, b₂₃, e]
    rw [datumMap_comp]
    simp only [u₂₃, pr₂, pullback.lift_snd]
    rw [datumMap_f, datumMap_f]
    exact isPullback_eqToHom_conj (IsPullback.of_hasPullback (f₂ l m) (f n))
      (obj_U D (f₃ l m n) (h₃ l m n)) (obj_U D (f₂ l m) (h₂ l m)) (obj_U D (f n) (hR n))
  obtain ⟨Z₀, q₀, hq₀, g₀, hsq₀, hg₀⟩ := FiniteCover.exists_descended_of_diagram
    P fP hfpqc' Q c e sq₂ T b₁₂ b₂₃ b₁₃ hc₁ hc₂ hc₃ sq₃
  let pq (l : L) : (P l).Z ⟶ V l := (P l).q ≫ eqToHom (obj_U D (f l) (hR l))
  have hsq₀' (l : L) : IsPullback (g₀ l) (H.map (pq l)) q₀ (H.map (f l)) :=
    isPullback_map_eqToHom_of_cover q₀ (V l) (P l) (obj_U D (f l) (hR l)) (f l) (g₀ l) (hsq₀ l)
  obtain ⟨Zs, qs, g, hqs, hsq, hgl⟩ :=
    exists_site_cover_of_scheme_cocone f pq q₀ d hq₀ g₀ hsq₀'
  obtain ⟨ζ, hζlift, hζg⟩ :
      ∃ ζ : ∀ l, (D.obj (f l) (hR l)).1 ⟶ (⟨U, Zs, qs, hqs⟩ : FiniteCover B S hS d),
        (∀ l, (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (f l) (ζ l)) ∧ ∀ l, (ζ l).g = g l := by
    refine ⟨fun l ↦ ⟨eqToHom (obj_U D (f l) (hR l)) ≫ f l, g l,
      isPullback_of_comp_eqToHom _ _ _ _ _ (hsq l)⟩, fun l ↦ ?_, fun _ ↦ rfl⟩
    refine isHomLift_of_f_eq (Q := (⟨U, Zs, qs, hqs⟩ : FiniteCover B S hS d)) _
      (obj_U D (f l) (hR l)) (f l) ?_
    rfl
  refine ⟨⟨U, Zs, qs, hqs⟩, rfl, ζ, hζlift, ?_⟩
  intro A l m b hb a a' ha ha'
  refine hom_ext_of_isHomLift b _ _ ?_ ?_ ?_
  · exact isHomLift_datumMap_comp D (hR l) hb a ha _ (hζlift l)
  · exact isHomLift_datumMap_comp D (hR m) hb a' ha' _ (hζlift m)
  · show (datumMap D (hR l) hb a ha).g ≫ (ζ l).g =
      (datumMap D (hR m) hb a' ha').g ≫ (ζ m).g
    rw [hζg, hζg]
    refine hgl l m _ _ ?_
    have hlift : pullback.lift a a' (ha.trans ha'.symm) ≫ f₂ l m = b := by
      dsimp only [f₂, pr₁]
      rw [← Category.assoc, pullback.lift_fst]
      exact ha
    have hm₁ : datumMap D (h₂ l m) hb (pullback.lift a a' (ha.trans ha'.symm)) hlift ≫ c l m =
        datumMap D (hR l) hb a ha := by
      dsimp only [c]
      rw [datumMap_comp]
      simp only [pr₁, pullback.lift_fst]
    have hm₂ : datumMap D (h₂ l m) hb (pullback.lift a a' (ha.trans ha'.symm)) hlift ≫ e l m =
        datumMap D (hR m) hb a' ha' := by
      dsimp only [e]
      rw [datumMap_comp]
      simp only [pr₂, pullback.lift_snd]
    have hm₁g : (datumMap D (h₂ l m) hb (pullback.lift a a' (ha.trans ha'.symm)) hlift).g ≫
        (c l m).g = (datumMap D (hR l) hb a ha).g := congrArg FiniteCover.Hom.g hm₁
    have hm₂g : (datumMap D (h₂ l m) hb (pullback.lift a a' (ha.trans ha'.symm)) hlift).g ≫
        (e l m).g = (datumMap D (hR m) hb a' ha').g := congrArg FiniteCover.Hom.g hm₂
    rw [← hm₁g, ← hm₂g, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      hg₀ l m]

/-- **Condition (3) of Stacks 026F for `ℋ_d`, along a covering family that is fpqc on underlying
schemes.** Every descent datum relative to the sieve generated by such a family is effective: the
descended cover is the object the datum descends to, the cartesian morphism out of the object at an
arrow of the sieve is the transport of the datum along a chosen factorization of that arrow
followed by the morphism at the corresponding member of the family, and the compatibility in a
single variable that `CategoryTheory.Functor.SieveDescentDatum.descends_of_isoAlong` asks for is
the gluing identity of the descended cover. -/
private lemma sieveDescentDatum_isEffective_of_fpqc_family {U : BigFppfOver B S hS}
    {L : Type v} {V : L → BigFppfOver B S hS} (f : ∀ l, V l ⟶ U)
    (hfpqc : Presieve.ofArrows (fun l ↦ (BigFppfOver.toScheme B S hS).obj (V l))
      (fun l ↦ (BigFppfOver.toScheme B S hS).map (f l)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U))
    (D : SieveDescentDatum
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) (Sieve.ofArrows V f)) :
    D.IsEffective := by
  classical
  have hR (l : L) : (Sieve.ofArrows V f) (f l) := Sieve.ofArrows_mk V f l
  obtain ⟨cv, hcv, ζfam, hζfam, hζcompat⟩ :=
    exists_descended_cover_of_fpqc_family D f hR hfpqc
  have hex : ∀ (A : BigFppfOver B S hS) (h : A ⟶ U), (Sieve.ofArrows V f).arrows h →
      ∃ (l : L) (b : A ⟶ V l), b ≫ f l = h :=
    fun _ _ hh ↦ Functor.exists_factorization_of_ofArrows hh
  choose idx arr harr using hex
  obtain ⟨ζ, hζdef⟩ :
      ∃ ζ : ∀ ⦃A : BigFppfOver B S hS⦄ (h : A ⟶ U) (hh : (Sieve.ofArrows V f).arrows h),
        (D.obj h hh).1 ⟶ cv,
        ∀ ⦃A : BigFppfOver B S hS⦄ (h : A ⟶ U) (hh : (Sieve.ofArrows V f).arrows h),
          ζ h hh = datumMap D (hR (idx A h hh)) hh (arr A h hh) (harr A h hh) ≫
            ζfam (idx A h hh) :=
    ⟨fun {A} h hh ↦ datumMap D (hR (idx A h hh)) hh (arr A h hh) (harr A h hh) ≫
      ζfam (idx A h hh), fun _ _ _ ↦ rfl⟩
  refine (SieveDescentDatum.isEffective_iff_exists_descends
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) D).mpr
    ⟨Functor.Fiber.mk hcv, ζ,
      D.descends_of_isoAlong (Functor.Fiber.mk hcv) ζ (fun {A} h hh ↦ ?_) ?_⟩
  · have h₃ := isHomLift_datumMap_comp D (hR (idx A h hh)) hh (arr A h hh) (harr A h hh) _
      (hζfam (idx A h hh))
    rw [hζdef h hh]
    have h₄ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsStronglyCartesian
        h (datumMap D (hR (idx A h hh)) hh (arr A h hh) (harr A h hh) ≫
          ζfam (idx A h hh)) := by
      have := h₃
      exact (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
        (d := d)).isStronglyCartesian_homLift h _
    exact Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ h _
  · intro A A' h hh γ b hb hb'
    have habs : Functor.Fiber.fiberInclusion.map (D.contract hh γ hb' hb).hom ≫
        datumMap D hh hb' γ hb = IsPreFibered.pullbackMap (D.obj h hh).2 γ := by
      show Functor.Fiber.fiberInclusion.map (D.contract hh γ hb' hb).hom ≫
        Functor.Fiber.fiberInclusion.map (D.contract hh γ hb' hb).inv ≫
          IsPreFibered.pullbackMap (D.obj h hh).2 γ = _
      rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hkey := hζcompat (idx A' b hb') (idx A h hh) hb' (arr A' b hb') (γ ≫ arr A h hh)
      (harr A' b hb') (by rwa [Category.assoc, harr A h hh])
    rw [hζdef b hb', hkey, hζdef h hh, ← habs]
    simp only [Category.assoc]
    rw [← Category.assoc (datumMap D hh hb' γ hb), datumMap_comp]

end Descent

/-! ### Condition (3) of Stacks 05WB for the category of finite locally free covers -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- **Condition (3) of Stacks 05WB for the category `ℋ_d` of degree-`d` finite locally free
covers: every descent datum is effective.** Let `{f i : V i ⟶ U}` be a covering family of the big
fppf site over `S` with genuine fibre-product double and triple overlaps, indexed by an arbitrary
type, and let `D` be a descent datum for `ℋ_d` relative to it. Then `D` is effective: there is a
degree-`d` finite locally free cover of `U` whose restrictions to the members of the family are
the covers of `D`, compatibly with its gluing isomorphisms.

The covering is first refined by a family whose underlying morphisms of schemes form an fpqc
covering family, which is legitimate because the `Isom` presheaves of `ℋ_d` are sheaves — that is
condition (2) of Stacks 05WB,
`AlgebraicGeometry.Stack.isMorSheaf_finiteCoverProjection`, and it does not consume effective
descent. Over such a refinement the datum *is* a diagram of covers of the kind that
`AlgebraicGeometry.Stack.FiniteCover.exists_descended_of_diagram` descends, by Tag 0245 for
schemes with affine structure morphisms and Tag 02VO for the rank. -/
theorem descentDatum_isEffective_finiteCoverProjection {U : BigFppfOver B S hS} {I : Type w}
    (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (Vij : I → I → BigFppfOver B S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → BigFppfOver B S hS)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : Functor.DescentDatum (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
      V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    D.IsEffective := by
  let : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
    Functor.IsFiberedInGroupoids.isFibered
      (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
  refine Functor.DescentDatum.isEffective_of_refinements
    (isMorSheaf_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    (fun {W} R hR ↦ ?_) D hf
  obtain ⟨L, V', f', hle, hcov, hfpqc⟩ := BigFppfOver.exists_fpqc_family_refining R hR
  exact ⟨Sieve.ofArrows V' f', Sieve.ofArrows_le_of_forall_mem V' f' hle, hcov,
    fun D' ↦ sieveDescentDatum_isEffective_of_fpqc_family f' hfpqc D'⟩

end AlgebraicGeometry.Stack

end

end
