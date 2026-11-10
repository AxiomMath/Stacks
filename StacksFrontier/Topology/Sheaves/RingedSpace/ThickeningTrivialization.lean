module

public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical trivialization of a complex of first order thickenings (Stacks 08LE)

Let `(X, 𝒪_X)` be a ringed space and let

    (X₁, 𝒪_{X₁}) ⟶ (X₂, 𝒪_{X₂}) ⟶ (X₃, 𝒪_{X₃})

be a complex of first order thickenings of `X` in the sense of
`AlgebraicGeometry.RingedSpaceThickening.IsComplex`. Then the composite
`(X₁, 𝒪_{X₁}) ⟶ (X₃, 𝒪_{X₃})` factors through `(X, 𝒪_X) ⟶ (X₃, 𝒪_{X₃})`, and the factor is a
retraction of `i₁`. So `(X₁, 𝒪_{X₁})` is a trivial first order thickening of `X` and comes with
a canonical trivialization.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.mono_of_isThickening`: a thickening of ringed spaces
  is a monomorphism.
* `AlgebraicGeometry.RingedSpaceThickening.comp_unitToPushforwardObjUnit_eq_zero_iff`: the
  one-step and two-step readings of a composite comorphism vanish together.
* `AlgebraicGeometry.RingedSpaceThickening.exists_factorization_of_comp_idealι_eq_zero`: a
  morphism into the ambient space of a thickening whose comorphism kills the kernel ideal
  factors through the thickening.
* `FirstOrderThickeningSequence.existsUnique_trivialization_of_isComplex`: **Stacks 08LE**, the
  canonical trivialization of a complex of first order thickenings.

## Implementation notes

The two steps of the source argument are separated. The first is about modules: the complex
condition on the chosen maps `ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁` is transported to the composite of the two *ambient*
ideal maps `(f₁₂)^* ℐ₂ ⟶ ℐ₁` of Tag 08KZ, using that for a first order thickening the unit of
`i^* ⊣ i_*` at the kernel ideal is an isomorphism (`isIso_unit_app_idealSheaf`). Transport goes
through `pullbackComparison₁₂` and `pullbackComparison₂₃`, which are `modulePullbackCompUniq` of
Tag 0097 followed by the transport along `i₁ ≫ f₁₂ = i₂` resp. `i₂ ≫ f₂₃ = i₃`;
`HasInducedIdealMaps` is exactly what identifies the chosen maps with the ambient ones.

The second step turns the vanishing `ℐ₃ ⟶ 𝒪_{X₃} ⟶ (f₁₂ ≫ f₂₃)_* 𝒪_{X₁}` into a factorization
of ringed spaces. The comorphism of a thickening is an epimorphism of sheaves of rings and its
underlying map is a homeomorphism, so a factorization of `𝒪_{X₃} ⟶ f_* 𝒪_{X₁}` through
`𝒪_{X₃} ⟶ (i₃)_* 𝒪_X` exists as a map of sheaves of rings and assembles into a morphism of
ringed spaces. Only additivity of the factor is formal; multiplicativity is checked on the
covering sieve over which both arguments lift, which is where epimorphy is used.

The morphism of ringed spaces is produced by rewriting the lower map's underlying continuous map
as `b ≫ i₃.base` before anything else, so that the base components of the two sides of the
required identity are *literally* equal and the `eqToHom` that `SheafedSpace.ext` would
otherwise interpose never appears.

## References

* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local implicit_reducible] RingedSpaceModuleAdjunction.modulePushforward
  RingedSpaceModuleAdjunction.modulePullback

/-! ### A thickening is a monomorphism, and factoring through it -/

/-- The comorphism `𝒪_{X'} ⟶ i_* 𝒪_X` of a thickening is locally surjective as a map of sheaves
of commutative rings. This is `isLocallySurjective_of_isThickening` read in the `CommRingCat`
spelling: local surjectivity is a condition on the underlying maps of sets, and the two
spellings of the comorphism have the same underlying maps. -/
theorem isLocallySurjective_comorphism_of_isThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsThickening i) : TopCat.Presheaf.IsLocallySurjective i.hom.c := by
  have h := isLocallySurjective_of_isThickening i hi
  constructor
  intro U s
  exact h.imageSieve_mem s

/-- A thickening of ringed spaces is a monomorphism. Two morphisms into `X` that agree after
composing with `i` have the same underlying map, because the underlying map of `i` is a
homeomorphism; and they have the same comorphism, because the comorphism of `i` is an
epimorphism of sheaves of rings. -/
theorem mono_of_isThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsThickening i) : Mono i := by
  have hiso : IsIso i.hom.base := hi.1
  constructor
  intro Y p q hpq
  have hb : p.hom.base = q.hom.base :=
    (cancel_mono i.hom.base).1 (congrArg (fun k => k.hom.base) hpq)
  rcases p with ⟨⟨bp, cp⟩⟩
  rcases q with ⟨⟨bq, cq⟩⟩
  change bp = bq at hb
  subst hb
  suffices h : cp = cq by cases h; rfl
  apply (TopCat.Presheaf.presheafEquivOfIso CommRingCat
    (asIso i.hom.base)).functor.map_injective
  let H := (TopCat.Sheaf.pushforward CommRingCat bp).obj Y.sheaf
  let a : X.sheaf ⟶ H := ⟨cp⟩
  let b : X.sheaf ⟶ H := ⟨cq⟩
  let Q := TopCat.Sheaf.pushforward CommRingCat i.hom.base
  let t : X'.sheaf ⟶ Q.obj X.sheaf := ⟨i.hom.c⟩
  have hts : Sheaf.IsLocallySurjective t := isLocallySurjective_comorphism_of_isThickening i hi
  have hte : Epi t := Sheaf.epi_of_isLocallySurjective t
  suffices h : Q.map a = Q.map b from congrArg (fun k => k.hom) h
  apply (cancel_epi t).1
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  have h := SheafedSpace.congr_hom_app hpq U
  simp only [eqToHom_map] at h
  exact h

/-- A map of sheaves of rings out of `G` is determined by an additive map on sections when it is
required to factor a ring map `f : F ⟶ H` through a locally surjective `q : F ⟶ G`. Only
multiplicativity has content: it is checked on the covering sieve over which both arguments
lift along `q`, using that `H` is separated. -/
private theorem exists_ringHom_of_additive_factorization
    {X : TopCat.{u}} (F G H : TopCat.Sheaf RingCat.{u} X)
    (q : F ⟶ G) (f : F ⟶ H)
    (hq : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) q.hom)
    (g : G.obj ⋙ forget₂ RingCat AddCommGrpCat ⟶ H.obj ⋙ forget₂ RingCat AddCommGrpCat)
    (hcomp : Functor.whiskerRight q.hom (forget₂ RingCat AddCommGrpCat) ≫ g =
      Functor.whiskerRight f.hom (forget₂ RingCat AddCommGrpCat)) :
    ∃ g' : G.obj ⟶ H.obj, Functor.whiskerRight g' (forget₂ RingCat AddCommGrpCat) = g := by
  let φ (U) : G.obj.obj U →+ H.obj.obj U := (g.app U).hom
  have nat {U V} (k : U ⟶ V) (b : G.obj.obj U) :
      φ V ((G.obj.map k).hom b) = (H.obj.map k).hom (φ U b) :=
    congrArg (fun z => z.hom b) (g.naturality k)
  have fac (U) (a : F.obj.obj U) :
      φ U ((q.hom.app U).hom a) = (f.hom.app U).hom a :=
    congrArg (fun z => (z.app U).hom a) hcomp
  let η : G.obj ⟶ H.obj :=
    { app := fun U => RingCat.ofHom
        { __ := φ U
          map_one' := (congrArg (φ U) (q.hom.app U).hom.map_one).symm.trans
            ((fac U 1).trans (f.hom.app U).hom.map_one)
          map_mul' := by
            intro b c
            have hS : Presheaf.imageSieve q.hom b ⊓ Presheaf.imageSieve q.hom c ∈
                Opens.grothendieckTopology X (unop U) :=
              (Opens.grothendieckTopology X).intersection_covering
                (hq.imageSieve_mem b) (hq.imageSieve_mem c)
            apply H.isSeparated (unop U) _ hS
            intro V p hp
            obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hp
            change (H.obj.map p.op).hom (φ U (b * c)) =
              (H.obj.map p.op).hom (φ U b * φ U c)
            rw [(H.obj.map p.op).hom.map_mul, ← nat p.op, ← nat p.op, ← nat p.op,
              (G.obj.map p.op).hom.map_mul]
            change φ (op V) ((G.obj.map p.op).hom b * (G.obj.map p.op).hom c) = _
            rw [← ha, ← ha', ← (q.hom.app (op V)).hom.map_mul,
              fac, fac, fac, (f.hom.app (op V)).hom.map_mul] }
      naturality := by
        intro U V p
        ext x
        exact nat p x }
  exact ⟨η, by ext U x; rfl⟩

/-- A factorization of comorphisms over a thickening `i` assembles into a factorization of
morphisms of ringed spaces. The underlying map of `f` is first rewritten as `b ≫ i.hom.base`,
which is possible because `i.hom.base` is an isomorphism; the comorphism of the factor is then
the one supplied by fullness of pushforward along the homeomorphism `i.hom.base`. -/
private theorem exists_factorization_of_comorphism_factorization
    {X Y X' : RingedSpace.{u, u}} (i : X ⟶ X') (f : Y ⟶ X')
    [IsIso i.hom.base]
    (g : (TopCat.Presheaf.pushforward CommRingCat i.hom.base).obj X.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat f.hom.base).obj Y.presheaf)
    (hg : i.hom.c ≫ g = f.hom.c) :
    ∃ p : Y ⟶ X, p ≫ i = f := by
  obtain ⟨⟨fb, fc⟩⟩ := f
  obtain ⟨b, hb⟩ : ∃ b, b ≫ i.hom.base = fb := ⟨fb ≫ inv i.hom.base, by simp⟩
  subst hb
  have hfull : (TopCat.Presheaf.pushforward CommRingCat i.hom.base).Full :=
    inferInstanceAs
      (TopCat.Presheaf.presheafEquivOfIso CommRingCat (asIso i.hom.base)).functor.Full
  let P := TopCat.Presheaf.pushforward CommRingCat i.hom.base
  let g' : P.obj X.presheaf ⟶
      P.obj ((TopCat.Presheaf.pushforward CommRingCat b).obj Y.presheaf) := g
  have key : i.hom.c ≫ P.map (P.preimage g') = fc :=
    (congrArg (fun z => i.hom.c ≫ z) (Functor.map_preimage P g')).trans hg
  exact ⟨⟨⟨b, P.preimage g'⟩⟩,
    congrArg (fun z => (⟨⟨b ≫ i.hom.base, z⟩⟩ : Y ⟶ X')) key⟩

/-- **Stacks Project, Tag 08KZ.** Let `i : X ⟶ X'` be a thickening and `f : Y ⟶ X'` a morphism
of ringed spaces whose comorphism kills the kernel ideal `ℐ = ker(i^♯)`. Then `f` factors
through `i`.

The factorization of sheaves of modules exists because `i^♯` is an epimorphism killed by `ℐ`,
which is what `Abelian.epiDesc` supplies; `exists_ringHom_of_additive_factorization` upgrades
its underlying additive map to a map of sheaves of rings. -/
@[stacks 08KZ "factoring through a thickening"]
theorem exists_factorization_of_comp_idealι_eq_zero
    {X Y X' : RingedSpace.{u, u}} (i : X ⟶ X') (f : Y ⟶ X')
    (hi : IsThickening i)
    (h : kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) = 0) :
    ∃ p : Y ⟶ X, p ≫ i = f := by
  let q := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)
  let r := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)
  have hq : Epi q := hi.2.1
  let G := ((opensMap i).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology X'.carrier) (Opens.grothendieckTopology X.carrier)).obj
      (structureSheafRing X)
  let H := ((opensMap f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology X'.carrier) (Opens.grothendieckTopology Y.carrier)).obj
      (structureSheafRing Y)
  let g : G.obj ⋙ forget₂ RingCat AddCommGrpCat ⟶
      H.obj ⋙ forget₂ RingCat AddCommGrpCat :=
    (PresheafOfModules.toPresheaf (structureSheafRing X').obj).map (Abelian.epiDesc q r h).val
  have hg : Functor.whiskerRight (structureSheafHom i).hom
        (forget₂ RingCat AddCommGrpCat) ≫ g =
      Functor.whiskerRight (structureSheafHom f).hom (forget₂ RingCat AddCommGrpCat) := by
    have he := congrArg
      (fun k => (PresheafOfModules.toPresheaf (structureSheafRing X').obj).map k.val)
      (Abelian.comp_epiDesc q r h)
    exact he
  obtain ⟨η, hη⟩ := exists_ringHom_of_additive_factorization
    (structureSheafRing X') G H (structureSheafHom i) (structureSheafHom f)
    (isLocallySurjective_of_isThickening i hi) g hg
  let c : (TopCat.Presheaf.pushforward CommRingCat i.hom.base).obj X.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat f.hom.base).obj Y.presheaf :=
    { app := fun U => CommRingCat.ofHom (η.app U).hom
      naturality := by
        intro U V k
        ext x
        exact congrArg (fun z => z.hom x) (η.naturality k) }
  have hc : i.hom.c ≫ c = f.hom.c := by
    ext U x
    have he := congrArg (fun k => (k.app (op U)) ((i.hom.c.app (op U)).hom x)) hη
    have hh := congrArg (fun k => (k.app (op U)) x) hg
    exact he.trans hh
  have hiso : IsIso i.hom.base := hi.1
  exact exists_factorization_of_comorphism_factorization i f c hc

/-- The two readings of a composite comorphism agree on vanishing: `(g)_* (f)_* 𝒪_A` and
`(f ≫ g)_* 𝒪_A` have the same sections, and the two-step and the one-step comorphism are the
same map of sections, so a composite into one vanishes exactly when the corresponding composite
into the other does. -/
theorem comp_unitToPushforwardObjUnit_eq_zero_iff {A B C : RingedSpace.{u, u}}
    (f : A ⟶ B) (g : B ⟶ C) {M : SheafOfModules.{u} (structureSheafRing C)}
    (j : M ⟶ SheafOfModules.unit (structureSheafRing C)) :
    j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) ≫
        (modulePushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) = 0 ↔
      j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (f ≫ g)) = 0 := by
  constructor <;> intro h <;> ext U m <;> exact congrArg (fun k => (k.val.app U).hom m) h

/-! ### Transporting the complex condition to the ambient ideal maps -/

namespace MorphismOfThickenings

/-- The ambient ideal map `(f')^* J ⟶ I` of **Stacks 08KZ**, pulled back along `i`, computed
through a chosen presentation `c` of the reduced pullback `f^* t^* J`. The hypothesis `h` is the
defining property of an induced map `k` on ideal modules; the conclusion reads the pulled back
ambient map as that induced map. -/
theorem pullback_idealMap_eq
    (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t)
    (M : SheafOfModules.{u} (structureSheafRing D.X))
    (c : M ≅ (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))
    (k : M ⟶ (modulePullback D.i).obj D.idealI)
    (h : (modulePushforward D.i).map c.hom ≫ (D.firstOrderIdealMap hi ht).1 ≫
      (modulePullbackPushforwardAdjunction D.i).unit.app D.idealI =
      (modulePushforward D.i).map k) :
    (modulePullback D.i).map D.idealMap.1 =
      D.reducedPullbackComparison.hom ≫ c.inv ≫ k := by
  let R := modulePushforward D.i
  let adj := modulePullbackPushforwardAdjunction D.i
  have hm : (D.firstOrderIdealMap hi ht).1 ≫ adj.unit.app D.idealI =
      R.map c.inv ≫ R.map k := by
    apply (cancel_epi (R.map c.hom)).1
    simpa only [Category.assoc, ← R.map_comp_assoc, c.hom_inv_id, R.map_id,
      Category.id_comp] using h
  have hfs : D.firstOrderSurjection hi ht =
      adj.unit.app ((modulePullback D.f').obj D.idealJ) ≫
        R.map D.reducedPullbackComparison.hom := rfl
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality D.idealMap.1
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn, ← (D.firstOrderIdealMap hi ht).property.1, Category.assoc, hm, hfs,
    Category.assoc]
  simp only [Functor.map_comp]
  rfl

/-- The transpose of `idealMap` composed with the inclusion `I ⟶ 𝒪_{X'}` is the inclusion
`J ⟶ 𝒪_{S'}` followed by `(f')^♯`. This is the specification of `idealMap` of **Stacks 08KZ**
moved across the adjunction `(f')^* ⊣ (f')_*`. -/
theorem homEquiv_idealMap_comp_idealι (D : MorphismOfThickenings.{u}) :
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
        (D.idealMap.1 ≫
          kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i))) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.f') := by
  rw [D.idealMap.property]
  have hra : (SheafOfModules.pushforward (structureSheafHom D.f')).IsRightAdjoint :=
    modulePushforward_isRightAdjoint D.f'
  change (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
    ((modulePullback D.f').map _ ≫ SheafOfModules.pullbackObjUnitToUnit _) = _
  rw [Adjunction.homEquiv_naturality_left]
  congr 1
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- A version of `pullback_idealMap_eq` where the reduced pullback comparison is given as a
transport `e` followed by `c`. -/
private theorem pullback_idealMap_eq_of_comparison
    (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t)
    (M : SheafOfModules.{u} (structureSheafRing D.X))
    (c : M ≅ (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))
    (k : M ⟶ (modulePullback D.i).obj D.idealI)
    (h : (modulePushforward D.i).map c.hom ≫ (D.firstOrderIdealMap hi ht).1 ≫
      (modulePullbackPushforwardAdjunction D.i).unit.app D.idealI =
      (modulePushforward D.i).map k)
    (e : (modulePullback D.i).obj ((modulePullback D.f').obj D.idealJ) ⟶ M)
    (he : D.reducedPullbackComparison.hom = e ≫ c.hom) :
    (modulePullback D.i).map D.idealMap.1 = e ≫ k := by
  rw [pullback_idealMap_eq D hi ht M c k h, he, Category.assoc, Iso.hom_inv_id_assoc]

end MorphismOfThickenings

namespace FirstOrderThickeningSequence

attribute [local implicit_reducible] square₁₂ square₂₃

variable (S : FirstOrderThickeningSequence.{u})

/-- The ambient ideal map `(f₁₂)^* ℐ₂ ⟶ ℐ₁` of **Stacks 08KZ** attached to the first morphism of
the sequence, with its source and target spelled on `X₁` and `X₂` rather than through the
projections of `square₁₂`. -/
noncomputable def ambientIdealMap₁₂ :
    (modulePullback S.f₁₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂) ⟶
      AlgebraicGeometry.SheafOfModules.idealSheaf S.i₁ :=
  S.square₁₂.idealMap.1

/-- The ambient ideal map `(f₂₃)^* ℐ₃ ⟶ ℐ₂` attached to the second morphism of the sequence. -/
noncomputable def ambientIdealMap₂₃ :
    (modulePullback S.f₂₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃) ⟶
      AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂ :=
  S.square₂₃.idealMap.1

/-- The natural isomorphism `(f₁₂)^* ∘ (i₁)^* ≅ (i₂)^*` given by functoriality of pullback
(**Stacks 0097**) and the relation `i₁ ≫ f₁₂ = i₂`. -/
noncomputable def pullbackComparison₁₂ :
    modulePullback S.f₁₂ ⋙ modulePullback S.i₁ ≅ modulePullback S.i₂ :=
  (modulePullbackCompUniq S.i₁ S.f₁₂).symm ≪≫ eqToIso (congrArg modulePullback S.comm₁₂)

/-- The natural isomorphism `(f₂₃)^* ∘ (i₂)^* ≅ (i₃)^*`, one step further along the
sequence. -/
noncomputable def pullbackComparison₂₃ :
    modulePullback S.f₂₃ ⋙ modulePullback S.i₂ ≅ modulePullback S.i₃ :=
  (modulePullbackCompUniq S.i₂ S.f₂₃).symm ≪≫ eqToIso (congrArg modulePullback S.comm₂₃)

/-- The reduced pullback comparison of the square `square₁₂` is `pullbackComparison₁₂` followed
by `idealComparison₂`: both sides are built from the same comparison isomorphisms and
composable transports along `i₁ ≫ f₁₂ = i₂`. -/
private theorem square₁₂_reducedPullbackComparison_hom :
    S.square₁₂.reducedPullbackComparison.hom =
      S.pullbackComparison₁₂.hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂) ≫
        S.idealComparison₂.hom := by
  dsimp only [MorphismOfThickenings.reducedPullbackComparison, pullbackComparison₁₂,
    idealComparison₂, square₁₂, MorphismOfThickenings.idealJ]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Category.assoc, eqToHom_trans_assoc]

/-- The analogue of `square₁₂_reducedPullbackComparison_hom` for the second square. -/
private theorem square₂₃_reducedPullbackComparison_hom :
    S.square₂₃.reducedPullbackComparison.hom =
      S.pullbackComparison₂₃.hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃) ≫
        S.idealComparison₃.hom := by
  dsimp only [MorphismOfThickenings.reducedPullbackComparison, pullbackComparison₂₃,
    idealComparison₃, square₂₃, MorphismOfThickenings.idealJ]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Category.assoc, eqToHom_trans_assoc]

/-- The ambient ideal map of the first square, pulled back to `X`, is the chosen induced map
`ℐ₂ ⟶ ℐ₁` read through `pullbackComparison₁₂`. -/
private theorem pullback_square₁₂_idealMap (h : S.HasInducedIdealMaps) :
    (modulePullback S.i₁).map S.ambientIdealMap₁₂ =
      S.pullbackComparison₁₂.hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₂) ≫
        S.idealMap₂₁ := by
  exact MorphismOfThickenings.pullback_idealMap_eq_of_comparison S.square₁₂
    S.firstOrder₁ S.firstOrder₂ _ S.idealComparison₂ S.idealMap₂₁ h.1 _
    S.square₁₂_reducedPullbackComparison_hom

/-- The ambient ideal map of the second square, pulled back to `X`, is the chosen induced map
`ℐ₃ ⟶ ℐ₂` read through `pullbackComparison₂₃`. -/
private theorem pullback_square₂₃_idealMap (h : S.HasInducedIdealMaps) :
    (modulePullback S.i₂).map S.ambientIdealMap₂₃ =
      S.pullbackComparison₂₃.hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₃) ≫
        S.idealMap₃₂ := by
  exact MorphismOfThickenings.pullback_idealMap_eq_of_comparison S.square₂₃
    S.firstOrder₂ S.firstOrder₃ _ S.idealComparison₃ S.idealMap₃₂ h.2 _
    S.square₂₃_reducedPullbackComparison_hom

/-- For a complex of first order thickenings, the composite of the two ambient ideal maps of
**Stacks 08KZ** vanishes. The unit of `(i₁)^* ⊣ (i₁)_*` at `ℐ₁` is an isomorphism, so it is
enough to check the vanishing after pulling back to `X`, where the two maps become the chosen
maps `ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁`, whose composite is zero by hypothesis. -/
private theorem ambient_idealMap_comp_eq_zero
    (h : S.HasInducedIdealMaps) (hz : S.idealMap₃₂ ≫ S.idealMap₂₁ = 0) :
    (modulePullback S.f₁₂).map S.ambientIdealMap₂₃ ≫ S.ambientIdealMap₁₂ = 0 := by
  have hg : (modulePullback S.i₁).map
      ((modulePullback S.f₁₂).map S.ambientIdealMap₂₃ ≫ S.ambientIdealMap₁₂) = 0 := by
    rw [Functor.map_comp, pullback_square₁₂_idealMap S h, ← Category.assoc]
    have hn := S.pullbackComparison₁₂.hom.naturality S.ambientIdealMap₂₃
    dsimp only [Functor.comp_map] at hn
    rw [hn, Category.assoc, pullback_square₂₃_idealMap S h, Category.assoc, hz, comp_zero,
      comp_zero]
  have hiso := isIso_unit_app_idealSheaf S.i₁ S.firstOrder₁
  have hn := (modulePullbackPushforwardAdjunction S.i₁).unit.naturality
    ((modulePullback S.f₁₂).map S.ambientIdealMap₂₃ ≫ S.ambientIdealMap₁₂)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hg, Functor.map_zero, comp_zero] at hn
  exact (cancel_mono ((modulePullbackPushforwardAdjunction S.i₁).unit.app
    (AlgebraicGeometry.SheafOfModules.idealSheaf S.i₁))).1 (hn.trans zero_comp.symm)

/-- For a complex of first order thickenings, the kernel ideal `ℐ₃` is killed by the comorphism
of the composite `f₁₂ ≫ f₂₃ : X₁ ⟶ X₃`. Transposing the vanishing of the composite of the two
ambient ideal maps across `(f₁₂)^* ⊣ (f₁₂)_*` and then `(f₂₃)^* ⊣ (f₂₃)_*` turns each ideal map
into the corresponding comorphism, by `homEquiv_idealMap_comp_idealι`. -/
private theorem idealι₃_comp_comorphism_eq_zero
    (hz : (modulePullback S.f₁₂).map S.ambientIdealMap₂₃ ≫ S.ambientIdealMap₁₂ = 0) :
    kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.i₃)) ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (S.f₁₂ ≫ S.f₂₃)) = 0 := by
  let j₁ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.i₁))
  let j₂ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.i₂))
  let j₃ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.i₃))
  let q₁₂ := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.f₁₂)
  let q₂₃ := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom S.f₂₃)
  let a₁₂ := modulePullbackPushforwardAdjunction S.f₁₂
  let a₂₃ := modulePullbackPushforwardAdjunction S.f₂₃
  have h12 : a₁₂.homEquiv _ _ (S.ambientIdealMap₁₂ ≫ j₁) = j₂ ≫ q₁₂ :=
    MorphismOfThickenings.homEquiv_idealMap_comp_idealι S.square₁₂
  have h23 : a₂₃.homEquiv _ _ (S.ambientIdealMap₂₃ ≫ j₂) = j₃ ≫ q₂₃ :=
    MorphismOfThickenings.homEquiv_idealMap_comp_idealι S.square₂₃
  have step₁ : a₁₂.homEquiv _ _
      (((modulePullback S.f₁₂).map S.ambientIdealMap₂₃ ≫ S.ambientIdealMap₁₂) ≫ j₁) =
      S.ambientIdealMap₂₃ ≫ j₂ ≫ q₁₂ := by
    rw [Category.assoc, Adjunction.homEquiv_naturality_left, h12]
  have step₂ : a₂₃.homEquiv _ _ (S.ambientIdealMap₂₃ ≫ j₂ ≫ q₁₂) =
      (j₃ ≫ q₂₃) ≫ (modulePushforward S.f₂₃).map q₁₂ := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right, h23]
  have hfin : (j₃ ≫ q₂₃) ≫ (modulePushforward S.f₂₃).map q₁₂ = 0 := by
    rw [← step₂, ← step₁, hz, zero_comp]
    simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [Category.assoc] at hfin
  exact (comp_unitToPushforwardObjUnit_eq_zero_iff S.f₁₂ S.f₂₃ j₃).1 hfin

/-- **Stacks Project, Tag 08LE.** A complex of first order thickenings of `(X, 𝒪_X)` canonically
trivializes its first thickening: the composite `X₁ ⟶ X₃` factors uniquely through
`i₃ : X ⟶ X₃`, and the factor `π : X₁ ⟶ X` is a retraction of `i₁`. -/
@[stacks 08LE "canonical trivialization of a complex"]
theorem existsUnique_trivialization_of_isComplex (hS : IsComplex S) :
    ∃! π : S.X₁ ⟶ S.X, (S.i₁ ≫ π = 𝟙 S.X) ∧ (π ≫ S.i₃ = S.f₁₂ ≫ S.f₂₃) := by
  obtain ⟨π, hπ⟩ := exists_factorization_of_comp_idealι_eq_zero S.i₃ (S.f₁₂ ≫ S.f₂₃)
    S.firstOrder₃.1 (idealι₃_comp_comorphism_eq_zero S (ambient_idealMap_comp_eq_zero S hS.1 hS.2))
  have hmono : Mono S.i₃ := mono_of_isThickening S.i₃ S.firstOrder₃.1
  refine ⟨π, ⟨?_, hπ⟩, ?_⟩
  · apply (cancel_mono S.i₃).1
    rw [Category.assoc, hπ, ← Category.assoc, S.comm₁₂, S.comm₂₃, Category.id_comp]
  · intro π' hπ'
    exact (cancel_mono S.i₃).1 (hπ'.2.trans hπ.symm)

end FirstOrderThickeningSequence

end AlgebraicGeometry.RingedSpaceThickening

end
