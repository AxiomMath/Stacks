module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentTowerSystem
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde

/-!
# Systems of coherent modules along isomorphic towers

Let `X` be a scheme and let `(Xₙ, iₙ, kₙ)` and `(Yₙ, jₙ, lₙ)` be two towers over it, in the sense
of `Stacks.CoherentTower`: morphisms `iₙ : Xₙ ⟶ Xₙ₊₁` and `kₙ : Xₙ ⟶ X` with `iₙ ≫ kₙ₊₁ = kₙ`,
and likewise for `Y`. Suppose the two towers are isomorphic over `X`: there are isomorphisms
`cₙ : Xₙ ≅ Yₙ` with `iₙ ≫ cₙ₊₁ = cₙ ≫ jₙ` and `cₙ ≫ lₙ = kₙ`. This file shows that restriction
along one tower is an equivalence exactly when restriction along the other is.

This is the step [Stacks, Tag 089A] needs that [Stacks, Tag 088F] does not supply. The tower of
[Stacks, Tag 089A] is an *abstract* tower `Xₙ` carrying morphisms `kₙ : Xₙ ⟶ X` that exhibit each
`Xₙ` as a fibre product `X ×_{Spec A} Sₙ`, whereas Grothendieck existence is proved — here and in
the source — for the canonical tower of honest fibre products `Yₙ = X ×_{Spec A} Sₙ`. The
comparison isomorphisms `cₙ` are the ones the universal property of the fibre product provides,
and transporting the equivalence along them is what this file does.

## Main definitions

* `Stacks.AmpleFormalSystemTowerComparison.transport` — the functor
  `ModuleSystem j ⥤ ModuleSystem i` that pulls a system back along the `cₙ`.
* `Stacks.AmpleFormalSystemTowerComparison.restrictionTransportIso` — the natural isomorphism
  `restriction j l hl ⋙ transport ≅ restriction i k hk`.

## Main results

* `Stacks.AmpleFormalSystemTowerComparison.full_transport` and `faithful_transport` — the
  transport is fully faithful when every `cₙ` is an isomorphism.
* `Stacks.AmpleFormalSystemTowerComparison.isEquivalence_restriction` — **the comparison**: if
  restriction along `(Yₙ, jₙ, lₙ)` is an equivalence then so is restriction along
  `(Xₙ, iₙ, kₙ)`.
* `Stacks.AmpleFormalSystemTowerComparison.pullbackCoherence` — the coherence identity the
  comparison rests on: the two canonical identifications of
  `l₂^* ∘ c₂^* ∘ i^*` with `k₁^*` agree.

## Implementation notes

The mathematical content is the coherence identity `pullbackCoherence`, and it is the only place
where the pseudofunctoriality of `ℱ ↦ ℱ|_{-}` is used:
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` of Mathlib, twice, once for the
factorisation `i ≫ c₂ ≫ l₂` and once for `c₁ ≫ j ≫ l₂`, linked by the hypothesis
`i ≫ c₂ = c₁ ≫ j`. Everything else is bookkeeping: the equalities of morphisms that the two
towers satisfy are substituted away, so that the `Scheme.Modules.pullbackCongr` isomorphisms they
would otherwise contribute become identities and only the associativity remains.

That `Scheme.Modules.pullback` along an isomorphism of schemes is an equivalence is
`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`, which is why that file is
imported; it adds three modules to the closure.

The passage from "fully faithful and essentially surjective" to `Functor.IsEquivalence` is made
for the *abstract* tower directly rather than by building an equivalence of the two system
categories: full faithfulness of `transport` carries fullness and faithfulness across, and
essential surjectivity comes from `CategoryTheory.Functor.essSurj_of_comp_fully_faithful` applied
to the transport in the other direction. This avoids the unit and counit of an equivalence of
system categories, each of which would need a coherence identity of its own.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AmpleFormalSystemTowerComparison

open Stacks.CoherentTower
open AlgebraicGeometry.Scheme.Modules (pullback pullbackComp pullbackCongr)

/-! ### Identifications among iterated pullback functors -/

/-- The associator of pullback functors is the identity: `Functor.comp` is strictly associative,
so this is only a change of bracketing. -/
public lemma associator_hom_eq_id {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) :
    (Functor.associator F G H).hom = 𝟙 _ := rfl

/-- The associator of pullback functors is the identity, in the inverse direction. -/
public lemma associator_inv_eq_id {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) :
    (Functor.associator F G H).inv = 𝟙 _ := rfl

attribute [local simp] associator_hom_eq_id associator_inv_eq_id

/-- **`Scheme.Modules.pullbackComp` is natural in its first morphism**, up to the identification
`Scheme.Modules.pullbackCongr` of pullbacks along equal morphisms. -/
@[reassoc]
public lemma whiskerLeft_pullbackCongr {P Q R : Scheme.{u}} {u u' : P ⟶ Q} (h : u = u')
    (v : Q ⟶ R) :
    Functor.whiskerLeft (pullback v) (pullbackCongr h).hom ≫ (pullbackComp u' v).hom =
      (pullbackComp u v).hom ≫
        (pullbackCongr (show u ≫ v = u' ≫ v by rw [h])).hom := by
  subst h
  simp [pullbackCongr]

/-- **Pulling back along `v` and then along `u` is pulling back along a morphism `w = u ≫ v`.**
This is `Scheme.Modules.pullbackComp` followed by the identification of `u ≫ v` with `w`. -/
public def pullbackCompIso {A B C : Scheme.{u}} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (h : u ≫ v = w) : pullback v ⋙ pullback u ≅ pullback w :=
  pullbackComp u v ≪≫ pullbackCongr h

/-- For the reflexive equation `u ≫ v = u ≫ v`, `pullbackCompIso` is `pullbackComp u v`. -/
@[simp]
public lemma pullbackCompIso_rfl {A B C : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C) :
    pullbackCompIso (rfl : u ≫ v = u ≫ v) = pullbackComp u v := by
  simp [pullbackCompIso, pullbackCongr]

/-- **Two factorisations of one morphism give isomorphic iterated pullback functors.** -/
public def pullbackCompIso₂ {A B B' C : Scheme.{u}} {u : A ⟶ B} {v : B ⟶ C} {u' : A ⟶ B'}
    {v' : B' ⟶ C} (h : u ≫ v = u' ≫ v') :
    pullback v ⋙ pullback u ≅ pullback v' ⋙ pullback u' :=
  pullbackComp u v ≪≫ pullbackCongr h ≪≫ (pullbackComp u' v').symm

variable {X₁ X₂ Y₁ Y₂ W : Scheme.{u}} (i : X₁ ⟶ X₂) (c₁ : X₁ ⟶ Y₁) (c₂ : X₂ ⟶ Y₂)
  (j : Y₁ ⟶ Y₂) (l : Y₂ ⟶ W)

/-- **The iterated pullback along a three-step factorisation `i ≫ c₂ ≫ l`**, assembled by
combining `c₂` with `l` first and then with `i`. -/
public def pullbackAssocIso :
    (pullback l ⋙ pullback c₂) ⋙ pullback i ≅ pullback (i ≫ c₂ ≫ l) :=
  Functor.isoWhiskerRight (pullbackComp c₂ l) (pullback i) ≪≫ pullbackComp i (c₂ ≫ l)

/-- The forward map of `pullbackAssocIso i c₂ l` is the whiskered forward map of
`pullbackComp c₂ l` followed by the forward map of `pullbackComp i (c₂ ≫ l)`. -/
@[simp]
public lemma pullbackAssocIso_hom :
    (pullbackAssocIso i c₂ l).hom =
      Functor.whiskerRight (pullbackComp c₂ l).hom (pullback i) ≫
        (pullbackComp i (c₂ ≫ l)).hom := rfl

/-- **The associativity axiom of the pullback pseudofunctor**, in the form used below: combining
`i` with `c₂` first and then with `l` agrees with combining `c₂` with `l` first. -/
@[reassoc]
public lemma whiskerLeft_pullbackComp_hom :
    Functor.whiskerLeft (pullback l) (pullbackComp i c₂).hom ≫
        (pullbackComp (i ≫ c₂) l).hom =
      (pullbackAssocIso i c₂ l).hom ≫ eqToHom (by simp) := by
  rw [← Iso.inv_comp_eq]
  simpa [pullbackAssocIso] using
    Scheme.Modules.pseudofunctor_associativity (f := i) (g := c₂) (h := l)

/-- `whiskerLeft_pullbackComp_hom` with the first factor inverted. -/
@[reassoc]
public lemma whiskerLeft_pullbackComp_inv :
    Functor.whiskerLeft (pullback l) (pullbackComp i c₂).inv ≫ (pullbackAssocIso i c₂ l).hom =
      (pullbackComp (i ≫ c₂) l).hom ≫ eqToHom (by simp) := by
  rw [← Functor.isoWhiskerLeft_inv, Iso.inv_comp_eq, Functor.isoWhiskerLeft_hom,
    whiskerLeft_pullbackComp_hom_assoc]
  simp

/-- **The coherence identity, in normalised form.** Given a second factorisation
`i ≫ c₂ = c₁ ≫ j`, the iterated pullback along `i ≫ c₂ ≫ l` may equally be assembled through
`c₁` and `j`. -/
public lemma pullbackAssocIso_hom_eq (hc : i ≫ c₂ = c₁ ≫ j)
    (h₁ : c₁ ≫ j ≫ l = i ≫ c₂ ≫ l) :
    (pullbackAssocIso i c₂ l).hom =
      Functor.whiskerLeft (pullback l) (pullbackCompIso₂ hc).hom ≫
        (pullbackAssocIso c₁ j l).hom ≫ (pullbackCongr h₁).hom := by
  simp only [pullbackCompIso₂, Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp,
    Category.assoc]
  rw [whiskerLeft_pullbackComp_inv_assoc, whiskerLeft_pullbackCongr_assoc hc l,
    whiskerLeft_pullbackComp_hom_assoc]
  simp [pullbackCongr]

/-- **The coherence identity.** Let `i ≫ c₂ = c₁ ≫ j`, `j ≫ l₂ = l₁`, `i ≫ k₂ = k₁`,
`c₁ ≫ l₁ = k₁` and `c₂ ≫ l₂ = k₂`. Then the two canonical identifications of
`l₂^* ∘ c₂^* ∘ i^*` with `k₁^*` — the one through `k₂` and the one through `j` and `l₁` —
agree.

This is the mathematical content of the comparison of the two towers: it is exactly the statement
that the comparison isomorphisms `cₙ` are compatible with the transition isomorphisms of a
restricted module. -/
public lemma pullbackCoherence {X₁ X₂ Y₁ Y₂ W : Scheme.{u}} {i : X₁ ⟶ X₂} {c₁ : X₁ ⟶ Y₁}
    {c₂ : X₂ ⟶ Y₂} {j : Y₁ ⟶ Y₂} {l₁ : Y₁ ⟶ W} {l₂ : Y₂ ⟶ W} {k₁ : X₁ ⟶ W} {k₂ : X₂ ⟶ W}
    (hc : i ≫ c₂ = c₁ ≫ j) (hl : j ≫ l₂ = l₁) (hk : i ≫ k₂ = k₁)
    (h₁ : c₁ ≫ l₁ = k₁) (h₂ : c₂ ≫ l₂ = k₂) :
    Functor.whiskerRight (pullbackCompIso h₂).hom (pullback i) ≫ (pullbackCompIso hk).hom =
      Functor.whiskerLeft (pullback l₂) (pullbackCompIso₂ hc).hom ≫
        Functor.whiskerRight (pullbackCompIso hl).hom (pullback c₁) ≫
          (pullbackCompIso h₁).hom := by
  subst hl
  subst h₂
  subst hk
  have h := pullbackAssocIso_hom_eq i c₁ c₂ j l₂ hc h₁
  simp only [pullbackCompIso, Iso.trans_hom, pullbackAssocIso_hom,
    Category.assoc] at h ⊢
  exact h

/-! ### Transport of systems along a morphism of towers -/

section Tower

variable {X : Scheme.{u}} {Xn Yn : ℕ → Scheme.{u}}
  (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1)) (j : ∀ n : ℕ, Yn n ⟶ Yn (n + 1))
  (c : ∀ n : ℕ, Xn n ⟶ Yn n) (k : ∀ n : ℕ, Xn n ⟶ X) (l : ∀ n : ℕ, Yn n ⟶ X)

/-- **Transport of systems of coherent modules along a morphism of towers.** A system `(ℱₙ, φₙ)`
along `(Yₙ, jₙ)` is sent to `(cₙ^* ℱₙ)` along `(Xₙ, iₙ)`, with the transition isomorphisms
obtained from `iₙ ≫ cₙ₊₁ = cₙ ≫ jₙ` and `φₙ`. -/
public def transport [∀ n : ℕ, IsLocallyNoetherian (Xn n)]
    (hc : ∀ n : ℕ, i n ≫ c (n + 1) = c n ≫ j n) : ModuleSystem j ⥤ ModuleSystem i where
  obj F :=
    { obj := fun n => (Scheme.Modules.pullback (c n)).obj (F.obj n)
      isCoherent := fun n =>
        haveI := F.isCoherent n
        isCoherent_pullback (c n) (F.obj n)
      transitionIso := fun n =>
        (pullbackCompIso₂ (hc n)).app (F.obj (n + 1)) ≪≫
          (Scheme.Modules.pullback (c n)).mapIso (F.transitionIso n) }
  map {F G} α :=
    { app := fun n => (Scheme.Modules.pullback (c n)).map (α.app n)
      comm := fun n => by
        have hnat := (pullbackCompIso₂ (hc n)).hom.naturality (α.app (n + 1))
        simp only [CategoryTheory.Functor.comp_map] at hnat
        dsimp only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom]
        rw [← Category.assoc, hnat, Category.assoc, ← CategoryTheory.Functor.map_comp,
          α.comm n, CategoryTheory.Functor.map_comp]
        exact (Category.assoc _ _ _).symm }
  map_id _ := ModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_id _ _)
  map_comp _ _ := ModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_comp _ _ _)

variable [∀ n : ℕ, IsLocallyNoetherian (Xn n)] (hc : ∀ n : ℕ, i n ≫ c (n + 1) = c n ≫ j n)

/-- **The transport along an isomorphism of towers is faithful**, because pullback along an
isomorphism of schemes is. -/
public lemma faithful_transport (hiso : ∀ n : ℕ, IsIso (c n)) :
    (transport i j c hc).Faithful := by
  refine ⟨fun {F G} {α β} h => ?_⟩
  refine ModuleSystem.Hom.ext (funext fun n => ?_)
  have := hiso n
  exact (Scheme.Modules.pullback (c n)).map_injective (congrFun (congrArg ModuleSystem.Hom.app h) n)

/-- **The transport along an isomorphism of towers is full.** A morphism of transported systems
has components in the image of the fully faithful functors `cₙ^*`, and the preimages form a
morphism of systems because `cₙ^*` is faithful and the comparison isomorphisms are natural. -/
public lemma full_transport (hiso : ∀ n : ℕ, IsIso (c n)) : (transport i j c hc).Full := by
  refine ⟨fun {F G} γ => ?_⟩
  have : ∀ n : ℕ, IsIso (c n) := hiso
  choose β hβ using fun n : ℕ =>
    CategoryTheory.Functor.Full.map_surjective (F := Scheme.Modules.pullback (c n)) (γ.app n)
  refine ⟨⟨β, fun n => ?_⟩, ModuleSystem.Hom.ext (funext fun n => hβ n)⟩
  apply (Scheme.Modules.pullback (c n)).map_injective
  have hnat := (pullbackCompIso₂ (hc n)).hom.naturality (β (n + 1))
  simp only [CategoryTheory.Functor.comp_map] at hnat
  have hγ := γ.comm n
  dsimp only [transport, Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom] at hγ
  rw [← hβ (n + 1), ← hβ n] at hγ
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← cancel_epi ((pullbackCompIso₂ (hc n)).hom.app (F.obj (n + 1)))]
  simp only [Category.assoc] at hγ ⊢
  rw [← reassoc_of% hnat]
  exact hγ

/-- **A morphism of systems whose components are isomorphisms is an isomorphism.** The inverse
components commute with the transition isomorphisms because the direct ones do. -/
public def moduleSystemIsoOfComponents {F G : ModuleSystem i}
    (e : ∀ n : ℕ, F.obj n ≅ G.obj n)
    (hcomm : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).map (e (n + 1)).hom ≫
      (G.transitionIso n).hom = (F.transitionIso n).hom ≫ (e n).hom) : F ≅ G where
  hom := { app := fun n => (e n).hom, comm := hcomm }
  inv :=
    { app := fun n => (e n).inv
      comm := fun n => by
        rw [← CategoryTheory.Functor.mapIso_inv, Iso.inv_comp_eq,
          CategoryTheory.Functor.mapIso_hom, reassoc_of% (hcomm n)]
        simp }
  hom_inv_id := ModuleSystem.Hom.ext (funext fun n => (e n).hom_inv_id)
  inv_hom_id := ModuleSystem.Hom.ext (funext fun n => (e n).inv_hom_id)

variable [∀ n : ℕ, IsLocallyNoetherian (Yn n)]
  (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n) (hl : ∀ n : ℕ, j n ≫ l (n + 1) = l n)
  (hkl : ∀ n : ℕ, c n ≫ l n = k n)

/-- **Restriction along `(Xₙ, iₙ, kₙ)` is restriction along `(Yₙ, jₙ, lₙ)` followed by the
transport.** The components are the identifications `cₙ^*(ℱ|_{Yₙ}) ≅ ℱ|_{Xₙ}` coming from
`cₙ ≫ lₙ = kₙ`, and that they commute with the transition isomorphisms is
`pullbackCoherence`. -/
public def restrictionTransportIso :
    restriction j l hl ⋙ transport i j c hc ≅ restriction i k hk :=
  NatIso.ofComponents
    (fun F => moduleSystemIsoOfComponents i (fun n => (pullbackCompIso (hkl n)).app F.obj)
      (fun n => NatTrans.congr_app
        (pullbackCoherence (hc n) (hl n) (hk n) (hkl n) (hkl (n + 1))) F.obj))
    (fun φ => ModuleSystem.Hom.ext (funext fun n =>
      (pullbackCompIso (hkl n)).hom.naturality φ.hom))

include hc hkl in
/-- **The comparison of the two towers.** If the two towers over `X` are isomorphic over `X`,
then restriction along one is an equivalence as soon as restriction along the other is.

Fullness and faithfulness transfer along `restrictionTransportIso`, since the transport is fully
faithful. Essential surjectivity is `CategoryTheory.Functor.essSurj_of_comp_fully_faithful`
applied to the transport in the other direction, whose composite with restriction along
`(Xₙ, iₙ, kₙ)` is isomorphic to restriction along `(Yₙ, jₙ, lₙ)`. -/
public lemma isEquivalence_restriction (hiso : ∀ n : ℕ, IsIso (c n))
    (hrj : (restriction j l hl).IsEquivalence) : (restriction i k hk).IsEquivalence := by
  have := hrj
  have : ∀ n : ℕ, IsIso (c n) := hiso
  have hc' : ∀ n : ℕ, j n ≫ CategoryTheory.inv (c (n + 1)) = CategoryTheory.inv (c n) ≫ i n :=
    fun n => by rw [IsIso.comp_inv_eq, Category.assoc, hc n, IsIso.inv_hom_id_assoc]
  have hlk : ∀ n : ℕ, CategoryTheory.inv (c n) ≫ k n = l n :=
    fun n => by rw [← hkl n, IsIso.inv_hom_id_assoc]
  have := full_transport i j c hc hiso
  have := faithful_transport i j c hc hiso
  have := full_transport j i (fun n => CategoryTheory.inv (c n)) hc' fun n => inferInstance
  have := faithful_transport j i (fun n => CategoryTheory.inv (c n)) hc' fun n => inferInstance
  have : (restriction i k hk).Full :=
    CategoryTheory.Functor.Full.of_iso (restrictionTransportIso i j c k l hc hk hl hkl)
  have : (restriction i k hk).Faithful :=
    CategoryTheory.Functor.Faithful.of_iso (restrictionTransportIso i j c k l hc hk hl hkl)
  have : (restriction i k hk ⋙
      transport j i (fun n => CategoryTheory.inv (c n)) hc').EssSurj :=
    CategoryTheory.Functor.essSurj_of_iso
      (restrictionTransportIso j i (fun n => CategoryTheory.inv (c n)) l k hc' hl hk hlk).symm
  have := CategoryTheory.Functor.essSurj_of_comp_fully_faithful (restriction i k hk)
    (transport j i (fun n => CategoryTheory.inv (c n)) hc')
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Tower

end Stacks.AmpleFormalSystemTowerComparison

end
