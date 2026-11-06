module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkFibreComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleUnboundedDerivations
public import StacksCore.Tactic.StacksAttribute

/-!
# The two maps of Stacks 0GIX are global sections of base change maps

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, and consider the diagram
of the source

```
X_s  ---ι--->  X ×_S Spec(𝒪^{sh}_{S,s})  ---p--->  X
|f_s                |f'                             |f
v                   v                               v
s    ---i--->  Spec(𝒪^{sh}_{S,s})         ---j--->  S
```

Stacks 0GIX *defines* its two canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

by taking global sections of the derived base change maps (Stacks 0A2A) of the right and of the
left square, and asserts that their composite is the usual base change map. This file makes those
definitions, proves the composition clause for them, and proves that they are the maps this
library constructs more directly
(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections` and
`AlgebraicGeometry.strictHenselizationSectionsToFibreSections`).

All derived functors are total right derived functors on the whole unbounded homotopy category.
None of the statements below takes their existence as a hypothesis: it is supplied by the
instances `Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` and
`Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb`, which hold because
abelian sheaves on a small étale site form a Grothendieck abelian category and so have
K-injective resolutions (Stacks 079P, 070K).

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleUnboundedDerivedBaseChangeAb` — the derived base change map of
  Stacks 0A2A of an arbitrary commutative square, read in the vocabulary of
  `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb`.
* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange` —
  **[Stacks, Tag 0GIX], the first map**: the comparison of the stalk with derived sections over the
  strict henselization (an isomorphism, `AlgebraicGeometry.isIso_vanishingCyclesMap_id`), followed
  by derived global sections over the strict henselization of the base change map of the right
  square and by `RΓ(Spec 𝒪^{sh}_{S,s}, Rf'_* -) ≅ RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, -)`.
* `AlgebraicGeometry.strictHenselizationSectionsToFibreSectionsViaBaseChange` —
  **[Stacks, Tag 0GIX], the second map**: `RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, -) ≅
  RΓ(Spec 𝒪^{sh}_{S,s}, Rf'_* -)`, restriction along `i`, derived global sections on `s` of the
  base change map of the left square, and `RΓ(s, Rf_{s,*} -) ≅ RΓ(X_s, -)`.

## Main results

* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange_comp` —
  **[Stacks, Tag 0GIX], the composition clause**: the composite of the two maps is the usual base
  change map `(Rf_*K)_s ⟶ RΓ(X_s, K|_{X_s})`.
* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_eq_baseChange` and
  `AlgebraicGeometry.strictHenselizationSectionsToFibreSections_eq_baseChange` — the maps this
  library constructs directly are the two maps of the source.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_eq_baseChange` — for an
  arbitrary commutative square, derived restriction of global sections along its top is derived
  global sections of its base change map; the second map is the instance at the left square.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb_baseChange` and
  `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_eq_baseChange` — the two
  underived identities the derived statements reduce to.

## Implementation notes

Every derived statement is proved by `CategoryTheory.Functor.rightDerived_ext` out of a right
derived functor (`RΓ(X', -)` for the second map, the stalk of `Rf_*` for the first) and reduced, by
the factorization properties of the maps involved, to an underived identity, which is checked on
sections (for the left square) or on germs (for the right square) with
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb`. The derived base
change map is characterized through
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_conj_fac`, which is stated at a generic
coefficient universe for the reason recorded in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedStalkFibreComposition.lean`.

*One proof term per square.* A statement in which the same square appears with two different
proofs of its commutativity (for instance `h` and `h.symm.symm`) around a concrete base change map
is, in practice, beyond the kernel's budget, even though proofs are irrelevant. So the right square is
recorded once, as `AlgebraicGeometry.strictHenselizationBaseChange_square`, in the orientation the
0A2A map takes it, and every statement uses that term or its `symm`.

*The structure morphism as `𝟙 ≫ j`.* The comparison of the stalk with sections over the strict
henselization, `AlgebraicGeometry.vanishingCyclesMap`, is stated for a scheme over the strict
henselization, here the strict henselization itself via `𝟙`; the inverse image it produces is along
`𝟙 ≫ j`, so the right square is the square over `𝟙 ≫ j` (the same morphism as `j`).

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.DerivedFunctor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]

/-- The comparison of homotopy categories attached to `e : F ⋙ G ≅ H`, followed by the
degreewise action of `τ : H ⟶ N ⋙ K`, is the degreewise action of `e.hom ≫ τ`. -/
public theorem mapHomotopyCategoryCompIso_hom_app_comp_ofComp (F : A₁ ⥤ A₂) [F.Additive]
    (G : A₂ ⥤ A₃) [G.Additive] (H : A₁ ⥤ A₃) [H.Additive] (N : A₁ ⥤ A₄) [N.Additive]
    (K : A₄ ⥤ A₃) [K.Additive] (e : F ⋙ G ≅ H) (τ : H ⟶ N ⋙ K)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J ≫
        (mapHomotopyCategoryOfComp H N K τ).app J =
      (mapHomotopyCategoryOfComp (F ⋙ G) N K (e.hom ≫ τ)).app J := by
  rw [mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app]
  show (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map _ ≫
    (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map _ = _
  rw [← Functor.map_comp]
  congr 1

/-- The inverse comparison attached to `e : F ⋙ G ≅ H`, followed by the degreewise action of
`e.hom ≫ τ`, is the degreewise action of `τ`. -/
public theorem mapHomotopyCategoryCompIso_inv_app_comp_ofComp (F : A₁ ⥤ A₂) [F.Additive]
    (G : A₂ ⥤ A₃) [G.Additive] (H : A₁ ⥤ A₃) [H.Additive] (N : A₁ ⥤ A₄) [N.Additive]
    (K : A₄ ⥤ A₃) [K.Additive] (e : F ⋙ G ≅ H) (τ : H ⟶ N ⋙ K)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app J ≫
        (mapHomotopyCategoryOfComp (F ⋙ G) N K (e.hom ≫ τ)).app J =
      (mapHomotopyCategoryOfComp H N K τ).app J := by
  rw [← mapHomotopyCategoryCompIso_hom_app_comp_ofComp F G H N K e τ J, Iso.inv_hom_id_app_assoc]

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### The derived base change map of a commutative square, in the small-étale vocabulary -/

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The derived base change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` of a commutative square
`g' ≫ f = f' ≫ g` of schemes, on unbounded derived categories of abelian sheaves on the small
étale sites: the map `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` of Stacks 0A2A, read
in the vocabulary of `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb` through the
identifications of the two inverse images. For the cartesian square defining a geometric fibre
this is `AlgebraicGeometry.geometricFibreDerivedBaseChangeAb`. -/
def smallEtaleUnboundedDerivedBaseChangeAb :
    smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedPullbackAb g ⟶
      smallEtaleDerivedPullbackAb g' ⋙ smallEtaleDerivedPushforwardAb f' :=
  Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
      (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g).hom ≫
    etaleAbelianDerivedBaseChange.{u, u + 1} f g g' f' h ≫
    Functor.whiskerRight (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g').inv
      (smallEtaleDerivedPushforwardAb f')

/-- The derived base change map of a commutative square at an object, written out. -/
theorem smallEtaleUnboundedDerivedBaseChangeAb_app (K : smallEtaleDerivedCategory X) :
    (smallEtaleUnboundedDerivedBaseChangeAb f g g' f' h).app K =
      (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g).hom.app
          ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (etaleAbelianDerivedBaseChange.{u, u + 1} f g g' f' h).app K ≫
        (smallEtaleDerivedPushforwardAb f').map
          ((smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g').inv.app K) := by
  have hdef : smallEtaleUnboundedDerivedBaseChangeAb f g g' f' h =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g).hom ≫
        etaleAbelianDerivedBaseChange.{u, u + 1} f g g' f' h ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g').inv
          (smallEtaleDerivedPushforwardAb f') := rfl
  rw [hdef]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rfl

/-- **The derived base change map of a commutative square, at a complex.** Precomposed with the
identification of the two actions of `g⁻¹` and with the unit of the derivation of `f_*`, the
derived base change map is the degreewise underived base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` followed by the unit of the derivation of
`f'_*`. -/
theorem smallEtaleUnboundedDerivedBaseChangeAb_fac
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtalePullbackAb g).mapDerivedCategoryFactorsh.inv.app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPullbackAb g).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (smallEtaleUnboundedDerivedBaseChangeAb f g g' f' h).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb f ⋙ smallEtalePullbackAb g) (smallEtalePullbackAb g')
          (smallEtalePushforwardAb f')
          (smallEtaleBaseChangeAb g f f' g' h.symm)).app J) ≫
        (smallEtaleDerivedPushforwardAbUnit f').app
          ((Functor.mapHomotopyCategory (smallEtalePullbackAb g') (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPushforwardAb f').map
          ((smallEtalePullbackAb g').mapDerivedCategoryFactorsh.inv.app J) := by
  refine (congrArg (fun t => _ ≫ _ ≫ t)
    (smallEtaleUnboundedDerivedBaseChangeAb_app f g g' f' h (DerivedCategory.Qh.obj J))).trans ?_
  exact etaleAbelianDerivedBaseChange_conj_fac.{u, u + 1} f g g' f' h _ _
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage g)
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage g')
    (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g)
    (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage g')
    (mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso g)
    (mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso_inv g') _
    (smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange g f f' g' h.symm) J

end BaseChange

/-- Conjugating a factorization by two isomorphisms, for bare morphisms. -/
private theorem conj_rearrange {C : Type*} [Category C] {A A' B B' C₁ D₁ D : C} (i : A ≅ A')
    (j : B ≅ B') {a : A ⟶ B} {b : A' ⟶ B'} {sPi : A' ⟶ C₁} {x : C₁ ⟶ D₁} {y : D₁ ⟶ D}
    {sPι : B' ⟶ D} {sbc : A' ⟶ D} (hpg : i.inv ≫ a = b ≫ j.inv) (h1 : sPi ≫ x ≫ y = sbc)
    (h2 : b ≫ sPι = sbc) : (i.hom ≫ sPi) ≫ x ≫ y = a ≫ j.hom ≫ sPι := by
  have ha : a = i.hom ≫ b ≫ j.inv := by rw [← hpg, Iso.hom_inv_id_assoc]
  rw [ha, Category.assoc, h1]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, h2]

/-- The rearrangement carrying the derived form of
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb_baseChange`, after the unit, to the
underived identity. Stated for bare morphisms in abstract categories. -/
private theorem restriction_rearrange {C C' C'' E : Type*} [Category C] [Category C']
    [Category C''] [Category E] (Rs : C ⥤ E) (Rq : C' ⥤ C) (RT : C'' ⥤ E)
    {A₀ A₁ A₂ A₃ A₅ A₆ A₇ B₀ : E} {M₀ M₁ : C''} {P₀ P₁ P₂ P₇ : C} {E₁ E₃ : C'}
    {uX : A₀ ⟶ A₁} {rι : A₁ ⟶ A₂} {ii : A₁ ⟶ RT.obj M₁} {ri : RT.obj M₁ ⟶ Rs.obj P₂}
    {b : P₂ ⟶ Rq.obj E₃} {io : Rs.obj (Rq.obj E₃) ⟶ A₂} {uT : B₀ ⟶ RT.obj M₀} {uf : M₀ ⟶ M₁}
    {ri₀ : RT.obj M₀ ⟶ Rs.obj P₁} {su : P₁ ⟶ P₂} {qri : B₀ ⟶ A₃} {uS : A₃ ⟶ Rs.obj P₀}
    {fi : P₀ ⟶ P₁} {w : P₀ ⟶ P₇} {uq : P₇ ⟶ Rq.obj E₁} {z : E₁ ⟶ E₃}
    {io₀ : Rs.obj (Rq.obj E₁) ⟶ A₅} {RYz : A₅ ⟶ A₂} {qΓY : A₃ ⟶ A₆} {uS' : A₆ ⟶ Rs.obj P₇}
    {qc : A₆ ⟶ A₇} {uY : A₇ ⟶ A₅} {ih : RT.obj M₁ ⟶ A₁} {qγ : B₀ ⟶ A₀} {qγ' : A₀ ⟶ B₀}
    {qrι : A₀ ⟶ A₇}
    (ha : RT.map uf ≫ ri = ri₀ ≫ Rs.map su) (hb : uT ≫ ri₀ = qri ≫ uS ≫ Rs.map fi)
    (hC : fi ≫ su ≫ b = w ≫ uq ≫ Rq.map z) (hi : Rs.map (Rq.map z) ≫ io = io₀ ≫ RYz)
    (hj : uS ≫ Rs.map w = qΓY ≫ uS') (hk : uS' ≫ Rs.map uq ≫ io₀ = qc ≫ uY)
    (hF : uT ≫ RT.map uf ≫ ih = qγ ≫ uX) (hih : ih ≫ ii = 𝟙 _) (hqγ : qγ' ≫ qγ = 𝟙 _)
    (hdeg : qγ' ≫ qri ≫ qΓY ≫ qc = qrι) (hL : uX ≫ rι = qrι ≫ uY ≫ RYz) :
    uX ≫ rι = uX ≫ ii ≫ ri ≫ Rs.map b ≫ io := by
  have hmain := Stacks.DerivedFunctor.fibreBaseChange_rearrange Rs Rq
    (stu := uT ≫ RT.map uf) (d₀ := uT ≫ ri₀) (φ := 𝟙 _)
    (by rw [Category.assoc, ha, Category.assoc]) (by rw [hb, Category.id_comp]) hC hi hj hk
  have hX : uX ≫ ii = qγ' ≫ uT ≫ RT.map uf := by
    rw [← Category.id_comp (uX ≫ ii), ← hqγ, Category.assoc, ← Category.assoc qγ uX ii,
      ← hF]
    simp only [Category.assoc, hih, Category.comp_id]
  rw [hL, ← Category.assoc uX ii, hX]
  simp only [Category.assoc] at hmain ⊢
  rw [hmain, Category.id_comp, ← hdeg]
  simp only [Category.assoc]

/-- Comparing two maps out of a stalk on a germ, for bare morphisms. -/
private theorem germ_eq {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C} {t : A₀ ⟶ A₁}
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {c : A₃ ⟶ A₄} {st : A₀ ⟶ A₂} {sp : A₀ ⟶ A₄} {L : A₁ ⟶ A₄}
    (hgerm : t ≫ a = st) (hsq : st ≫ b ≫ c = sp) (hrhs : t ≫ L = sp) :
    t ≫ a ≫ b ≫ c = t ≫ L := by
  rw [← Category.assoc, hgerm, hsq, hrhs]

/-! ### Restriction of sections along the top of a square is sections of the base change map -/

section Restriction

variable {Y X' P T : Scheme.{u}} (ι : Y ⟶ X') (f' : X' ⟶ T) (q : Y ⟶ P) (i : P ⟶ T)
  (w : ι ≫ f' = q ≫ i)

/-- The morphism `Y ⟶ T ×_T X'` with components `q ≫ i` and `ι`, into the base change along `f'`
of the identity object of the small étale site of `T`. -/
def squareLiftToBaseChangeId :
    Y ⟶ ((smallEtaleBaseChange f').obj (Scheme.Etale.mk (𝟙 T))).left :=
  pullback.lift (f := (Scheme.Etale.mk (𝟙 T)).hom) (g := f') (q ≫ i) ι
    ((Category.comp_id (q ≫ i)).trans w.symm)

/-- **Restriction of global sections along the top of a commutative square is the base change map
read on global sections.** For a commutative square `ι ≫ f' = q ≫ i` of schemes and an abelian
sheaf `F` on the small étale site of `X'`, restricting a global section of `F` to `Y` along `ι`
is: reading it as a global section of `f'_*F` on `T`, restricting it to `P` along `i`, applying
the base change map `i⁻¹f'_*F ⟶ q_*ι⁻¹F` and reading the result as a global section of `ι⁻¹F`
on `Y`. -/
theorem smallEtaleGlobalSectionsRestrictionAb_baseChange :
    Functor.whiskerLeft (smallEtalePushforwardAb f') (smallEtaleGlobalSectionsRestrictionAb i) ≫
        Functor.whiskerRight (smallEtaleBaseChangeAb i f' q ι w.symm)
          (Sheaf.Γ (smallEtaleTopology P) Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb ι) (smallEtalePushforwardGammaIsoAb q).hom =
      (smallEtalePushforwardGammaIsoAb f').hom ≫ smallEtaleGlobalSectionsRestrictionAb ι := by
  have hρ : squareLiftToBaseChangeId ι f' q i w ≫
      ((smallEtaleBaseChange f').obj (Scheme.Etale.mk (𝟙 T))).hom = ι :=
    pullback.lift_snd (f := (Scheme.Etale.mk (𝟙 T)).hom) (g := f') _ _ _
  have hfst : squareLiftToBaseChangeId ι f' q i w ≫ pullback.fst (Scheme.Etale.mk (𝟙 T)).hom f' =
      q ≫ i := pullback.lift_fst (f := (Scheme.Etale.mk (𝟙 T)).hom) (g := f') _ _ _
  have hsq := smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb i f' q ι w.symm
    (Scheme.Etale.mk (𝟙 T)) i (Category.comp_id i) (squareLiftToBaseChangeId ι f' q i w) hρ hfst
  -- the identification of the two lifts out of `Y`
  have hlift : ι ≫ (smallEtaleIdToBaseChangeIdIso f').hom.left =
      squareLiftToBaseChangeId ι f' q i w := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·)
        (smallEtaleIdToBaseChangeIdIso_hom_left_fst f')).trans (w.trans hfst.symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·)
        (pullback.lift_snd _ _ _ : (smallEtaleIdToBaseChangeIdIso f').hom.left ≫
          pullback.snd (Scheme.Etale.mk (𝟙 T)).hom f' = 𝟙 X')).trans
        ((Category.comp_id ι).trans
          (pullback.lift_snd (f := (Scheme.Etale.mk (𝟙 T)).hom) (g := f') _ _ _).symm))
  have hρ' : (ι ≫ (smallEtaleIdToBaseChangeIdIso f').hom.left) ≫
      ((smallEtaleBaseChange f').obj (Scheme.Etale.mk (𝟙 T))).hom = ι :=
    (congrArg (· ≫ _) hlift).trans hρ
  have hmap := map_comp_smallEtaleSectionsPullbackAb ι (Scheme.Etale.mk (𝟙 X')) ι
    (smallEtaleIdToBaseChangeIdIso f').hom (Category.comp_id ι) hρ'
  have hcongr := smallEtaleSectionsPullbackAb_congr ι
    ((smallEtaleBaseChange f').obj (Scheme.Etale.mk (𝟙 T)))
    (ι ≫ (smallEtaleIdToBaseChangeIdIso f').hom.left) hρ' hρ hlift
  refine NatTrans.ext (funext fun F => ?_)
  have e1 := congrArg (fun φ => NatTrans.app φ F) hsq
  have e2 := congrArg (fun φ => NatTrans.app φ F) (hmap.trans hcongr)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at e1 e2 ⊢
  exact conj_rearrange
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).app ((smallEtalePushforwardAb f').obj F))
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
      (isTerminalEtaleMkId X')).app F)
    (smallEtalePushforwardGammaIsoAb_hom_app f' F) e1 e2


/-- The degreewise part of the derived restriction along the top of a square. -/
theorem smallEtaleGlobalSectionsRestriction_baseChange_degreewise
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (.up ℤ)) :
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (smallEtalePushforwardGammaIsoAb f') (.up ℤ)).inv.app J) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtalePullbackAb i)
            (Sheaf.Γ (smallEtaleTopology P) Ab.{u + 1})
            (smallEtaleGlobalSectionsRestrictionAb i)).app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f') (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategory (Sheaf.Γ (smallEtaleTopology P) Ab.{u + 1}) (.up ℤ)).map
            ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
              (smallEtalePushforwardAb f' ⋙ smallEtalePullbackAb i) (smallEtalePullbackAb ι)
              (smallEtalePushforwardAb q) (smallEtaleBaseChangeAb i f' q ι w.symm)).app J)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (smallEtalePushforwardGammaIsoAb q) (.up ℤ)).hom.app
          ((Functor.mapHomotopyCategory (smallEtalePullbackAb ι) (.up ℤ)).obj J)) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (Sheaf.Γ (smallEtaleTopology X') Ab.{u + 1}) (smallEtalePullbackAb ι)
        (Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1})
        (smallEtaleGlobalSectionsRestrictionAb ι)).app J) := by
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
    ← DerivedCategory.Qh.map_comp,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three,
    smallEtaleGlobalSectionsRestrictionAb_baseChange ι f' q i w,
    Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_inv_app_comp_ofComp]

/-- **Restriction of derived global sections along the top of a commutative square is derived
global sections of the base change map.** For a commutative square `ι ≫ f' = q ≫ i` of schemes,
the derived restriction `RΓ(X', M) ⟶ RΓ(Y, ι⁻¹M)` is: the identification
`RΓ(X', M) ≅ RΓ(T, Rf'_*M)` of Stacks 0D6H, the derived restriction along `i`, derived global
sections on `P` of the derived base change map `i⁻¹Rf'_*M ⟶ Rq_*ι⁻¹M` of Stacks 0A2A, and the
identification `RΓ(P, Rq_* -) ≅ RΓ(Y, -)`. Nothing is assumed of the square beyond
commutativity, and `M` ranges over the whole unbounded derived category. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_eq_baseChange :
    smallEtaleDerivedGlobalSectionsRestriction ι =
      (smallEtaleDerivedGlobalSectionsPushforwardIsoAb f').inv ≫
        Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f')
          (smallEtaleDerivedGlobalSectionsRestriction i) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleUnboundedDerivedBaseChangeAb f' i ι q w)
          (smallEtaleDerivedGlobalSections P) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb ι)
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb q).hom := by
  refine Functor.rightDerived_ext (smallEtaleDerivedGlobalSections X')
    (smallEtaleDerivedGlobalSectionsUnit X')
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  refine NatTrans.ext (funext fun J => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  exact restriction_rearrange (smallEtaleDerivedGlobalSections P)
    (smallEtaleDerivedPushforwardAb q) (smallEtaleDerivedGlobalSections T)
    ((smallEtaleDerivedGlobalSectionsRestriction i).naturality
      ((smallEtaleDerivedPushforwardAbUnit f').app J))
    (smallEtaleDerivedGlobalSectionsRestriction_fac_app i
      ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f') (.up ℤ)).obj J))
    (smallEtaleUnboundedDerivedBaseChangeAb_fac f' i ι q w J)
    ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb q).hom.naturality
      ((smallEtalePullbackAb ι).mapDerivedCategoryFactorsh.inv.app J))
    ((smallEtaleDerivedGlobalSectionsUnit P).naturality
      ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb f' ⋙ smallEtalePullbackAb i) (smallEtalePullbackAb ι)
          (smallEtalePushforwardAb q) (smallEtaleBaseChangeAb i f' q ι w.symm)).app J)).symm
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app q
      ((Functor.mapHomotopyCategory (smallEtalePullbackAb ι) (.up ℤ)).obj J))
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app f' J)
    (Iso.hom_inv_id_app _ _)
    (by rw [← DerivedCategory.Qh.map_comp, Iso.inv_hom_id_app]; exact DerivedCategory.Qh.map_id _)
    (smallEtaleGlobalSectionsRestriction_baseChange_degreewise ι f' q i w J)
    (smallEtaleDerivedGlobalSectionsRestriction_fac_app ι J)

end Restriction

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-! ### The second map: the left square -/

/-- **Stacks 0GIX, the second map.** The canonical map
`RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`, natural in `K ∈ D(X_étale)`, defined as
the source defines it: from the derived base change map `i⁻¹Rf'_*(p⁻¹K) ⟶ Rf_{s,*}(K|_{X_s})` of
the left square

```
X_s ----> X ×_S Spec(𝒪^{sh}_{S,s})
|f_s             |f'
v                v
s  ---i--> Spec(𝒪^{sh}_{S,s})
```

by taking global sections: it is the identification
`RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), -) ≅ RΓ(Spec(𝒪^{sh}_{S,s}), Rf'_* -)`, restriction of derived
global sections along `i` (an isomorphism over the strictly henselian base), derived global
sections on `s` of the base change map, the identification `RΓ(s, Rf_{s,*} -) ≅ RΓ(X_s, -)`, and
the identification of the restriction of `p⁻¹K` to `X_s` with `K|_{X_s}`.

Every derived functor here is the total right derived functor on the whole unbounded homotopy
category; their existence is not assumed but supplied by the instances
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` and
`Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb` (abelian sheaves on a
small étale site have K-injective resolutions). -/
@[stacks 0GIX "the second map: global sections of the base change map for the left square"]
def strictHenselizationSectionsToFibreSectionsViaBaseChange :
    smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) ⟶
      smallEtaleDerivedPullbackAb (geometricFibreToSource f s) ⋙
        smallEtaleDerivedGlobalSections (geometricFibre f s) :=
  Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
      ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb
          (strictHenselizationBaseChangeToStrictHenselization B hS f s)).inv ≫
        Functor.whiskerLeft (smallEtaleDerivedPushforwardAb
            (strictHenselizationBaseChangeToStrictHenselization B hS f s))
          (smallEtaleDerivedGlobalSectionsRestriction
            (geometricPointToStrictHenselization B S hS s)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleUnboundedDerivedBaseChangeAb
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)
            (geometricPointToStrictHenselization B S hS s)
            (geometricFibreToStrictHenselizationBaseChange B hS f s)
            (geometricFibreToPoint f s)
            (geometricFibreToStrictHenselizationBaseChange_comp_toStrictHenselization B hS f s))
          (smallEtaleDerivedGlobalSections s.source) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb
            (geometricFibreToStrictHenselizationBaseChange B hS f s))
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb (geometricFibreToPoint f s)).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
        NatTrans.mapDerivedCategory (geometricFibrePullbackAbCompIso B hS f s).hom)
      (smallEtaleDerivedGlobalSections (geometricFibre f s))

/-- The second map of Stacks 0GIX as this library constructs it directly, by derived restriction
of global sections along `X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})`
(`AlgebraicGeometry.strictHenselizationSectionsToFibreSections`), is the map of the source: global
sections of the base change map for the left square. -/
theorem strictHenselizationSectionsToFibreSections_eq_baseChange :
    strictHenselizationSectionsToFibreSections B hS f s =
      strictHenselizationSectionsToFibreSectionsViaBaseChange B hS f s :=
  congrArg (fun t => Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)) t ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
            NatTrans.mapDerivedCategory (geometricFibrePullbackAbCompIso B hS f s).hom)
          (smallEtaleDerivedGlobalSections (geometricFibre f s)))
    (smallEtaleDerivedGlobalSectionsRestriction_eq_baseChange
      (geometricFibreToStrictHenselizationBaseChange B hS f s)
      (strictHenselizationBaseChangeToStrictHenselization B hS f s) (geometricFibreToPoint f s)
      (geometricPointToStrictHenselization B S hS s)
      (geometricFibreToStrictHenselizationBaseChange_comp_toStrictHenselization B hS f s))

/-! ### The first map: the right square -/

/-- The right square `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` over `Spec(𝒪^{sh}_{S,s}) ⟶ S`, with the
structure morphism of the strict henselization written as `𝟙 ≫ j`, the form in which the
identification of the stalk with sections over the strict henselization presents it. -/
theorem strictHenselizationBaseChange_square :
    strictHenselizationBaseChangeToSource B hS f s ≫ f =
      strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
        (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) :=
  pullback.condition.trans (congrArg (strictHenselizationBaseChangeToStrictHenselization B hS f s
      ≫ ·)
    (Category.id_comp _).symm)

/-- **The underived core of the first map.** The map on abelian sheaves
`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is the comparison `(f_*F)_s ⟶ Γ(Spec 𝒪^{sh}_{S,s},
j⁻¹f_*F)` of the stalk with sections over the strict henselization, followed by the base change
map of the right square read on global sections over the strict henselization. -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_eq_baseChange :
    Functor.whiskerLeft (smallEtalePushforwardAb f)
          (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s))) ≫
        Functor.whiskerRight
          (smallEtaleBaseChangeAb (𝟙 (strictHenselization B S hS s) ≫
              strictHenselizationToBase B S hS s) f
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)
            (strictHenselizationBaseChangeToSource B hS f s)
            (strictHenselizationBaseChange_square B hS f s).symm)
          (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtalePushforwardGammaIsoAb
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)).hom =
      pushforwardStalkToStrictHenselizationSectionsAb B hS f s := by
  refine NatTrans.ext (funext fun F => ?_)
  refine smallEtaleStalkAb_hom_ext s.hom ((smallEtalePushforwardAb f).obj F) fun W v => ?_
  have hρ : strictHenselizationBaseChangeEtaleLift B hS f s W v ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj W).hom =
          strictHenselizationBaseChangeToSource B hS f s :=
    pullback.lift_snd _ _ _
  have hfst : strictHenselizationBaseChangeEtaleLift B hS f s W v ≫ pullback.fst W.hom f =
      strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
        (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationNeighborhoodLift B S hS s W v) :=
    (pullback.lift_fst _ _ _).trans
      (congrArg (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫ ·)
        (Category.id_comp _).symm)
  have hsq := congrArg (fun φ => NatTrans.app φ F)
    (smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb
      (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) f
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (strictHenselizationBaseChangeToSource B hS f s)
      (strictHenselizationBaseChange_square B hS f s).symm W
      (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationNeighborhoodLift B S hS s W v)
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
      (strictHenselizationBaseChangeEtaleLift B hS f s W v) hρ hfst)
  have hgerm := etaleStalkToSectionsAb_toPresheafFiber B S hS s (𝟙 (strictHenselization B S hS s))
    ((smallEtalePushforwardAb f).obj F) W v
  have hrhs := pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS f s W v F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hsq ⊢
  exact germ_eq hgerm hsq hrhs

/-- The comparison of the stalk with derived sections over the strict henselization, at the image
of a complex: the identification of the two actions of the stalk, the degreewise comparison, and
the unit of the derivation of global sections over the strict henselization. -/
theorem vanishingCyclesMap_id_app
    (M : HomotopyCategory (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ)) :
    (vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s))).app (DerivedCategory.Qh.obj
        M) =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (smallEtaleStalkAb s.hom)
            (smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B
                S hS s))
            (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1})
            (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)))).app M) ≫
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselization B S hS s)).app
              ((Functor.mapHomotopyCategory
                (smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫
                    strictHenselizationToBase B S hS s)) (.up ℤ)).obj M) ≫
            (smallEtaleDerivedGlobalSections (strictHenselization B S hS s)).map
              ((smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase
                  B S hS s))
                |>.mapDerivedCategoryFactorsh.inv.app M) :=
  Stacks.DerivedFunctor.eq_comp_of_inv_comp (Iso.hom_inv_id_app _ _)
    (vanishingCyclesMap_fac_app B S hS s (𝟙 (strictHenselization B S hS s)) M)

/-- The degreewise part of the first map: the comparison of the stalk with sections over the
strict henselization, the base change map of the right square on sections over the strict
henselization, and the identification of sections of a direct image compose to the degreewise
action of the map on sheaves out of which the first map is descended. -/
theorem stalkStrictHenselizationDegreewise_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb s.hom)
          (smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S
              hS s))
          (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1})
          (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)))).app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategory (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
              s)) Ab.{u + 1})
            (.up ℤ)).map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
              (smallEtalePushforwardAb f ⋙
                smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase
                    B S hS s))
              (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
              (smallEtalePushforwardAb (strictHenselizationBaseChangeToStrictHenselization B hS f
                  s))
              (smallEtaleBaseChangeAb (𝟙 (strictHenselization B S hS s) ≫
                  strictHenselizationToBase B S hS s) f
                (strictHenselizationBaseChangeToStrictHenselization B hS f s)
                (strictHenselizationBaseChangeToSource B hS f s)
                (strictHenselizationBaseChange_square B hS f s).symm)).app J)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (smallEtalePushforwardGammaIsoAb
              (strictHenselizationBaseChangeToStrictHenselization B hS f s)) (.up ℤ)).hom.app
          ((Functor.mapHomotopyCategory
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj
                J)) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
        (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)).app J) := by
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three,
    pushforwardStalkToStrictHenselizationSectionsAb_eq_baseChange]

/-- The first map, precomposed with the unit, agrees with global sections of the base change map
of the right square at the image of every complex. -/
theorem derivedPushforwardStalkToStrictHenselizationSections_baseChange_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
          (DerivedCategory.Qh.obj J) =
      (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s))).app
          ((smallEtaleDerivedPushforwardAb f).obj (DerivedCategory.Qh.obj J)) ≫
        (smallEtaleDerivedGlobalSections (strictHenselization B S hS s)).map
          ((smallEtaleUnboundedDerivedBaseChangeAb f
              (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
              (strictHenselizationBaseChangeToSource B hS f s)
              (strictHenselizationBaseChangeToStrictHenselization B hS f s)
              (strictHenselizationBaseChange_square B hS f s)).app
            (DerivedCategory.Qh.obj J)) ≫
        (smallEtaleDerivedGlobalSectionsPushforwardIsoAb
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)).hom.app
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj
            (DerivedCategory.Qh.obj J)) := by
  refine (derivedPushforwardStalkToStrictHenselizationSections_fac_app B hS f s J).trans
    ((stalkSectionsUnit_app B hS f s J).trans ?_)
  have hR := Stacks.DerivedFunctor.fibreBaseChange_rearrange
    (smallEtaleDerivedGlobalSections (strictHenselization B S hS s))
    (smallEtaleDerivedPushforwardAb (strictHenselizationBaseChangeToStrictHenselization B hS f s))
    ((vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s))).naturality
      ((smallEtaleDerivedPushforwardAbUnit f).app J))
    (vanishingCyclesMap_id_app B hS s
      ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J))
    (smallEtaleUnboundedDerivedBaseChangeAb_fac f
      (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
      (strictHenselizationBaseChangeToSource B hS f s)
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (strictHenselizationBaseChange_square B hS f s) J)
    ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb
        (strictHenselizationBaseChangeToStrictHenselization B hS f s)).hom.naturality
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
        |>.mapDerivedCategoryFactorsh.inv.app J))
    ((smallEtaleDerivedGlobalSectionsUnit (strictHenselization B S hS s)).naturality
      ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb f ⋙
            smallEtalePullbackAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S
                hS s))
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtalePushforwardAb (strictHenselizationBaseChangeToStrictHenselization B hS f s))
          (smallEtaleBaseChangeAb (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B
              S hS s) f
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)
            (strictHenselizationBaseChangeToSource B hS f s)
            (strictHenselizationBaseChange_square B hS f s).symm)).app J)).symm
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      ((Functor.mapHomotopyCategory
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj J))
  refine Eq.trans ?_ hR.symm
  exact Stacks.DerivedFunctor.comp_three_middle _ _
    (stalkStrictHenselizationDegreewise_app B hS f s J)

/-- **Stacks 0GIX, the first map.** The canonical map
`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, natural in `K ∈ D(X_étale)`, defined as the
source defines it: from the derived base change map `j⁻¹Rf_*K ⟶ Rf'_*(p⁻¹K)` of the right square

```
X ×_S Spec(𝒪^{sh}_{S,s}) --p--> X
|f'                           |f
v                             v
Spec(𝒪^{sh}_{S,s}) ---j---> S
```

by taking global sections over the strict henselization: it is the comparison
`(Rf_*K)_s ⟶ RΓ(Spec(𝒪^{sh}_{S,s}), j⁻¹Rf_*K)` of the stalk with derived sections over the
strict henselization (`AlgebraicGeometry.vanishingCyclesMap`, an isomorphism by
`AlgebraicGeometry.isIso_vanishingCyclesMap_id`), derived global sections over the strict
henselization of the base change map, and the identification
`RΓ(Spec(𝒪^{sh}_{S,s}), Rf'_* -) ≅ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), -)`. The structure morphism `j` is
written `𝟙 ≫ j`, the form in which the comparison of the stalk with sections presents it.

Every derived functor here is the total right derived functor on the whole unbounded homotopy
category; their existence is not assumed but supplied by the instances
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` and
`Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb` (abelian sheaves on a
small étale site have K-injective resolutions). -/
@[stacks 0GIX "the first map: global sections of the base change map for the right square"]
def derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange :
    smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom ⟶
      smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) :=
  Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
      (vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleUnboundedDerivedBaseChangeAb f
        (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
        (strictHenselizationBaseChangeToSource B hS f s)
        (strictHenselizationBaseChangeToStrictHenselization B hS f s)
        (strictHenselizationBaseChange_square B hS f s))
      (smallEtaleDerivedGlobalSections (strictHenselization B S hS s)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
      (smallEtaleDerivedGlobalSectionsPushforwardIsoAb
        (strictHenselizationBaseChangeToStrictHenselization B hS f s)).hom

/-- The first map of Stacks 0GIX as this library constructs it directly, by descending the map on
sheaves `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb`
(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`), is the map of the
source: global sections of the base change map for the right square. -/
theorem derivedPushforwardStalkToStrictHenselizationSections_eq_baseChange :
    derivedPushforwardStalkToStrictHenselizationSections B hS f s =
      derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange B hS f s := by
  unfold derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange
  refine Functor.rightDerived_ext
    (smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom)
    (Functor.whiskerRight (smallEtaleDerivedPushforwardAbUnit f)
        (smallEtaleDerivedStalkAb s.hom) ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  refine NatTrans.ext (funext fun J => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  exact Stacks.DerivedFunctor.comp_id_comp_eq _
    (derivedPushforwardStalkToStrictHenselizationSections_baseChange_app B hS f s J)

/-! ### The composition -/

/-- **Stacks 0GIX, the composition clause.** For a morphism of schemes `f : X ⟶ S` and a
geometric point `s` of `S`, the composite of the two canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

obtained by taking global sections of the base change maps of the right and of the left square
(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange` and
`AlgebraicGeometry.strictHenselizationSectionsToFibreSectionsViaBaseChange`) is the usual base
change map `(Rf_*K)_s ⟶ RΓ(X_s, K|_{X_s})`: the identification of the stalk at `s` with global
sections on `s` of the inverse image, followed by global sections on `s` of the derived base change
map `s⁻¹Rf_*K ⟶ Rq_*(K|_{X_s})` of Stacks 0A2A for the cartesian square defining the geometric
fibre (`q : X_s ⟶ s` its structure morphism), and by the identification
`RΓ(s, Rq_* -) ≅ RΓ(X_s, -)` of Stacks 0D6H. This holds as an equality of natural transformations
on the whole unbounded derived category `D(X_étale)`; nothing is assumed of `f` or of `s`, and the
existence of the unbounded derived functors involved is supplied by instances, not assumed.

The two maps agree with the ones this library constructs directly
(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_eq_baseChange` and
`AlgebraicGeometry.strictHenselizationSectionsToFibreSections_eq_baseChange`), whose composite is
computed by
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_comp_fibreSections`. -/
@[stacks 0GIX "the composition is the base change map"]
theorem derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange_comp :
    derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange B hS f s ≫
        strictHenselizationSectionsToFibreSectionsViaBaseChange B hS f s =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (derivedGeometricStalkToPullbackSections s.hom) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (geometricFibreDerivedBaseChangeAb f s)
          (smallEtaleDerivedGlobalSections s.source) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb (geometricFibreToSource f s))
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb (geometricFibreToPoint f s)).hom := by
  rw [← derivedPushforwardStalkToStrictHenselizationSections_eq_baseChange,
    ← strictHenselizationSectionsToFibreSections_eq_baseChange]
  exact derivedPushforwardStalkToStrictHenselizationSections_comp_fibreSections B hS f s

end AlgebraicGeometry

end
