module

public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.Injective
public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemAbelian

/-!
# Every system of abelian sheaves embeds in one that is injective at each stage

A system of abelian sheaves `𝒜` over a fixed diagram `D` of spectral spaces
(`SpectralDiagram.AbelianSystem`) is a sheaf `𝒜ⱼ` on each space together with `f_a`-maps
`𝒜ᵢ ⟶ (f_a)_*𝒜ⱼ`.  This file constructs, for each choice of sheaves `ℐₖ` on the stages, the
**coinduced system**
```
𝒢ᵢ = ∏_{(k, b : k ⟶ i)} (f_b)_* ℐₖ,
```
whose `f_a`-map `𝒢ᵢ ⟶ (f_a)_*𝒢ⱼ` sends the factor indexed by `c : k ⟶ j` to the factor indexed
by `c ≫ a : k ⟶ i`, read through the identification `(f_{c ≫ a})_* = (f_a)_*(f_c)_*`.  A family
of maps `𝒜ₖ ⟶ ℐₖ` induces a morphism of systems `𝒜 ⟶ 𝒢`, and when each `ℐₖ` is injective and
each `𝒜ₖ ⟶ ℐₖ` is a monomorphism, `𝒢` is injective **at each stage** and `𝒜 ⟶ 𝒢` is a
monomorphism.

## Main definitions

* `SpectralDiagram.coindSheaf`: the sheaf `𝒢ᵢ` at a stage.
* `SpectralDiagram.coindPush`: its `f_a`-map.
* `SpectralDiagram.coindSystem`: the coinduced system itself.
* `SpectralDiagram.AbelianSystem.toCoind`: the morphism `𝒜 ⟶ 𝒢` induced by a family
  `𝒜ₖ ⟶ ℐₖ`.

## Main results

* `SpectralDiagram.injective_coindSheaf`: `𝒢ᵢ` is injective when each `ℐₖ` is.
* `SpectralDiagram.AbelianSystem.mono_toCoind`: `𝒜 ⟶ 𝒢` is a monomorphism when each
  `𝒜ₖ ⟶ ℐₖ` is.
* `SpectralDiagram.AbelianSystem.exists_mono_stageInjective`: every system admits a monomorphism
  into a system that is injective at each stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace TopCat.Presheaf

variable {C : Type*} [Category C] {X : TopCat.{u}} (P : X.Presheaf C)

/-- Three restriction maps of a presheaf around a cycle of opens compose to the identity. -/
theorem map_comp₃_eq_id {U V W : Opens X} (f : op U ⟶ op V) (g : op V ⟶ op W)
    (h : op W ⟶ op U) : P.map f ≫ P.map g ≫ P.map h = 𝟙 (P.obj (op U)) :=
  (congrArg (fun t => P.map f ≫ t) (P.map_comp g h).symm).trans
    ((P.map_comp f (g ≫ h)).symm.trans
      ((congrArg P.map (Subsingleton.elim _ (𝟙 (op U)))).trans (P.map_id (op U))))

/-- A threefold and a twofold composite of restriction maps of a presheaf between the same two
opens agree. -/
theorem map_comp₃_eq_map_comp {U V W Z V' : Opens X} (f : op U ⟶ op V) (g : op V ⟶ op W)
    (h : op W ⟶ op Z) (f' : op U ⟶ op V') (g' : op V' ⟶ op Z) :
    P.map f ≫ P.map g ≫ P.map h = P.map f' ≫ P.map g' :=
  (congrArg (fun t => P.map f ≫ t) (P.map_comp g h).symm).trans
    ((P.map_comp f (g ≫ h)).symm.trans
      ((congrArg P.map (Subsingleton.elim _ (f' ≫ g'))).trans (P.map_comp f' g')))

end TopCat.Presheaf

namespace SpectralDiagram

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}

/-! ### Morphisms of abelian sheaves on a stage, read at an open -/

/-- Composition of morphisms of abelian sheaves on a stage is computed at each open. -/
theorem comp_hom_app {i : J} {S T W : D.StageSheaf i} (φ : S ⟶ T) (ψ : T ⟶ W)
    (V : Opens (D.F.obj i)) :
    (φ ≫ ψ).hom.app (op V) = φ.hom.app (op V) ≫ ψ.hom.app (op V) := rfl

/-- The identity morphism of an abelian sheaf on a stage is the identity at each open. -/
theorem id_hom_app {i : J} (S : D.StageSheaf i) (V : Opens (D.F.obj i)) :
    (𝟙 S : S ⟶ S).hom.app (op V) = 𝟙 (S.presheaf.obj (op V)) := rfl

/-! ### The comparison maps of pushforward functors are restrictions -/

/-- The comparison `(f_{b ≫ a})_*G ⟶ (f_a)_*(f_b)_*G` is a restriction map of `G`. -/
theorem pushCompHom_hom_app {k j i : J} (b : k ⟶ j) (a : j ⟶ i) (G : D.StageSheaf k)
    (V : Opens (D.F.obj i)) :
    ((D.pushCompHom b a).app G).hom.app (op V) =
      G.presheaf.map ((D.preCompNatTrans b a).app (op V)) :=
  congrArg G.presheaf.map (Subsingleton.elim _ _)

/-- The comparison `(f_{𝟙})_*(f_c)_*G ⟶ (f_c)_*G` is a restriction map of `G`. -/
theorem pushIdHom_pushFunctor_hom_app {k j : J} (c : k ⟶ j) (G : D.StageSheaf k)
    (V : Opens (D.F.obj j)) :
    ((D.pushIdHom j).app ((D.pushFunctor c).obj G)).hom.app (op V) =
      G.presheaf.map ((Opens.map (D.F.map c)).op.map ((D.preIdNatTrans j).app (op V))) :=
  congrArg G.presheaf.map (Subsingleton.elim _ _)

/-- The comparison `(f_{b ≫ a})_*(f_d)_*G ⟶ (f_a)_*(f_b)_*(f_d)_*G` is a restriction map of
`G`. -/
theorem pushCompHom_pushFunctor_hom_app {m k j i : J} (d : m ⟶ k) (b : k ⟶ j) (a : j ⟶ i)
    (G : D.StageSheaf m) (V : Opens (D.F.obj i)) :
    ((D.pushCompHom b a).app ((D.pushFunctor d).obj G)).hom.app (op V) =
      G.presheaf.map ((Opens.map (D.F.map d)).op.map ((D.preCompNatTrans b a).app (op V))) :=
  congrArg G.presheaf.map (Subsingleton.elim _ _)

/-- The pushforward of the comparison `(f_{d ≫ b})_*G ⟶ (f_b)_*(f_d)_*G` is a restriction map of
`G`. -/
theorem pushFunctor_map_pushCompHom_hom_app {m k j i : J} (d : m ⟶ k) (b : k ⟶ j) (a : j ⟶ i)
    (G : D.StageSheaf m) (V : Opens (D.F.obj i)) :
    ((D.pushFunctor a).map ((D.pushCompHom d b).app G)).hom.app (op V) =
      G.presheaf.map ((D.preCompNatTrans d b).app (op ((Opens.map (D.F.map a)).obj V))) :=
  congrArg G.presheaf.map (Subsingleton.elim _ _)

/-! ### The coinduced system -/

variable (ℐ : ∀ k : J, D.StageSheaf k)

/-- The factor of the coinduced sheaf at the stage `i` indexed by an arrow `b.2 : b.1 ⟶ i`,
namely `(f_{b.2})_*ℐ_{b.1}`. -/
abbrev coindFam (i : J) (b : Σ k : J, (k ⟶ i)) : D.StageSheaf i :=
  (D.pushFunctor b.2).obj (ℐ b.1)

/-- The coinduced sheaf at the stage `i`: the product `∏_{b : k ⟶ i} (f_b)_*ℐₖ` over all arrows
of the diagram into `i`. -/
abbrev coindSheaf (i : J) : D.StageSheaf i := ∏ᶜ coindFam ℐ i

/-- Transport of a projection of the coinduced sheaf along an equality `d = c` of index arrows:
if `Φ` and `Ψ` differ by a restriction map of `ℐₖ` at every open, then the composites of the
projections indexed by `d` and `c` with `Φ` and `Ψ` agree. -/
theorem pi_π_congr {i k : J} (d c : k ⟶ i) (h : d = c) {T : D.StageSheaf i}
    (Φ : (D.pushFunctor d).obj (ℐ k) ⟶ T) (Ψ : (D.pushFunctor c).obj (ℐ k) ⟶ T)
    (hΦΨ : ∀ (V : Opens (D.F.obj i))
        (e : op ((Opens.map (D.F.map c)).obj V) ⟶ op ((Opens.map (D.F.map d)).obj V)),
        (ℐ k).presheaf.map e ≫ Φ.hom.app (op V) = Ψ.hom.app (op V)) :
    Pi.π (coindFam ℐ i) ⟨k, d⟩ ≫ Φ = Pi.π (coindFam ℐ i) ⟨k, c⟩ ≫ Ψ := by
  subst h
  refine congrArg (fun t => Pi.π (coindFam ℐ i) ⟨k, d⟩ ≫ t) ?_
  refine InducedCategory.Hom.ext (NatTrans.ext (funext fun U => ?_))
  obtain ⟨V⟩ := U
  refine Eq.trans ?_ (hΦΨ V (𝟙 _))
  exact ((congrArg (fun t => t ≫ Φ.hom.app (op V)) ((ℐ k).presheaf.map_id _)).trans
    (Category.id_comp _)).symm

/-- The leg of the fan defining the `f_a`-map of the coinduced system: project to the factor
indexed by `c.2 ≫ a` and read it through the identification
`(f_{c.2 ≫ a})_* = (f_a)_*(f_{c.2})_*`. -/
def coindLeg {j i : J} (a : j ⟶ i) (c : Σ k : J, (k ⟶ j)) :
    coindSheaf ℐ i ⟶ (D.pushFunctor a).obj (coindFam ℐ j c) :=
  Pi.π (coindFam ℐ i) ⟨c.1, c.2 ≫ a⟩ ≫ (D.pushCompHom c.2 a).app (ℐ c.1)

/-- The `f_a`-map of the coinduced system: the lift of the fan `coindLeg` against the product
`(f_a)_*𝒢ⱼ`. -/
def coindPush {j i : J} (a : j ⟶ i) :
    coindSheaf ℐ i ⟶ (D.pushFunctor a).obj (coindSheaf ℐ j) :=
  (isLimitOfHasProductOfPreservesLimit (D.pushFunctor a) (coindFam ℐ j)).lift
    (Fan.mk (coindSheaf ℐ i) (coindLeg ℐ a))

/-- The defining equation of the `f_a`-map of the coinduced system. -/
@[reassoc] theorem coindPush_π {j i : J} (a : j ⟶ i) (c : Σ k : J, (k ⟶ j)) :
    coindPush ℐ a ≫ (D.pushFunctor a).map (Pi.π (coindFam ℐ j) c) = coindLeg ℐ a c :=
  (isLimitOfHasProductOfPreservesLimit (D.pushFunctor a) (coindFam ℐ j)).fac _ ⟨c⟩

/-- The identity law of the coinduced system. -/
theorem coindPush_id (j : J) :
    coindPush ℐ (𝟙 j) ≫ (D.pushIdHom j).app (coindSheaf ℐ j) = 𝟙 (coindSheaf ℐ j) := by
  refine Pi.hom_ext _ _ fun c => ?_
  rw [Category.id_comp, Category.assoc, ← pushIdHom_naturality, ← Category.assoc, coindPush_π,
    coindLeg, Category.assoc]
  refine Eq.trans (pi_π_congr ℐ (c.2 ≫ 𝟙 j) c.2 (Category.comp_id c.2) _
    (𝟙 (coindFam ℐ j c)) fun V e => ?_) (Category.comp_id _)
  rw [comp_hom_app, pushCompHom_hom_app, pushIdHom_pushFunctor_hom_app, id_hom_app]
  exact (ℐ c.1).presheaf.map_comp₃_eq_id _ _ _

/-- The cocycle law of the coinduced system. -/
theorem coindPush_comp {k j i : J} (b : k ⟶ j) (a : j ⟶ i) :
    coindPush ℐ (b ≫ a) ≫ (D.pushCompHom b a).app (coindSheaf ℐ k) =
      coindPush ℐ a ≫ (D.pushFunctor a).map (coindPush ℐ b) := by
  refine (isLimitOfHasProductOfPreservesLimit (D.pushFunctor b ⋙ D.pushFunctor a)
    (coindFam ℐ k)).hom_ext fun e => ?_
  obtain ⟨e⟩ := e
  simp only [Fan.mk_π_app, Functor.comp_map, Category.assoc]
  rw [← pushCompHom_naturality, ← Functor.map_comp, coindPush_π_assoc, coindPush_π, coindLeg,
    coindLeg]
  simp only [Functor.map_comp, Category.assoc, coindPush_π_assoc, coindLeg]
  refine pi_π_congr ℐ (e.2 ≫ b ≫ a) ((e.2 ≫ b) ≫ a) (Category.assoc e.2 b a).symm _ _
    fun V f => ?_
  rw [comp_hom_app, comp_hom_app, pushCompHom_hom_app, pushCompHom_pushFunctor_hom_app,
    pushCompHom_hom_app, pushFunctor_map_pushCompHom_hom_app]
  exact (ℐ e.1).presheaf.map_comp₃_eq_map_comp _ _ _ _ _

/-- The coinduced system of abelian sheaves over `D`. -/
def coindSystem : D.AbelianSystem :=
  AbelianSystem.ofPushSheaf (coindSheaf ℐ) (coindPush ℐ) (coindPush_id ℐ)
    fun b a => coindPush_comp ℐ b a

/-- The sheaf of the coinduced system at the stage `i` is the coinduced sheaf. -/
@[simp] theorem coindSystem_sheaf (i : J) : (coindSystem ℐ).sheaf i = coindSheaf ℐ i := rfl

/-- The `f_a`-map of the coinduced system is `coindPush ℐ a`. -/
@[simp] theorem coindSystem_pushSheaf {j i : J} (a : j ⟶ i) :
    (coindSystem ℐ).pushSheaf a = coindPush ℐ a := rfl

/-- Each stage of the coinduced system is injective when each `ℐₖ` is. -/
instance injective_coindSheaf [∀ k : J, Injective (ℐ k)] (i : J) :
    Injective (coindSheaf ℐ i) :=
  inferInstance

/-! ### The morphism into the coinduced system -/

namespace AbelianSystem

variable (A : D.AbelianSystem) (ε : ∀ k : J, A.sheaf k ⟶ ℐ k)

/-- The component at the stage `i` of the morphism into the coinduced system: into the factor
indexed by `b.2 : b.1 ⟶ i` it is the `f_{b.2}`-map of `𝒜` followed by `(f_{b.2})_*ε`. -/
def toCoindApp (i : J) : A.sheaf i ⟶ coindSheaf ℐ i :=
  Pi.lift fun b => A.pushSheaf b.2 ≫ (D.pushFunctor b.2).map (ε b.1)

/-- The factor of the component at the stage `i` of the morphism into the coinduced system
indexed by `b.2 : b.1 ⟶ i` is the `f_{b.2}`-map of `𝒜` followed by `(f_{b.2})_*ε`. -/
@[reassoc] theorem toCoindApp_π (i : J) (b : Σ k : J, (k ⟶ i)) :
    toCoindApp ℐ A ε i ≫ Pi.π (coindFam ℐ i) b =
      A.pushSheaf b.2 ≫ (D.pushFunctor b.2).map (ε b.1) :=
  Pi.lift_π _ _

/-- The components of the morphism into the coinduced system commute with the `f_a`-maps. -/
theorem toCoindApp_push {j i : J} (a : j ⟶ i) :
    A.pushSheaf a ≫ (D.pushFunctor a).map (toCoindApp ℐ A ε j) =
      toCoindApp ℐ A ε i ≫ coindPush ℐ a := by
  refine (isLimitOfHasProductOfPreservesLimit (D.pushFunctor a) (coindFam ℐ j)).hom_ext
    fun c => ?_
  obtain ⟨c⟩ := c
  simp only [Fan.mk_π_app, Category.assoc, coindPush_π, coindLeg, toCoindApp_π_assoc,
    pushCompHom_naturality, ← Functor.map_comp, toCoindApp_π]
  rw [← Category.assoc _ _ (D.pushFunctor a |>.map _), A.pushSheaf_comp, Functor.map_comp,
    Category.assoc]

/-- The morphism of systems `𝒜 ⟶ 𝒢` induced by a family `𝒜ₖ ⟶ ℐₖ`. -/
def toCoind : A ⟶ coindSystem ℐ where
  app := toCoindApp ℐ A ε
  push_app a := toCoindApp_push ℐ A ε a

/-- The component at the stage `i` of the morphism into the coinduced system is
`toCoindApp ℐ A ε i`. -/
@[simp] theorem toCoind_app (i : J) : (toCoind ℐ A ε).app i = toCoindApp ℐ A ε i := rfl

/-- The morphism into the coinduced system is a monomorphism at each stage when each
`𝒜ₖ ⟶ ℐₖ` is. -/
instance mono_toCoindApp [∀ k : J, Mono (ε k)] (i : J) : Mono (toCoindApp ℐ A ε i) := by
  have hsplit : IsSplitMono (A.pushSheaf (𝟙 i)) :=
    IsSplitMono.mk' ⟨(D.pushIdHom i).app (A.sheaf i), A.pushSheaf_id i⟩
  have : Mono (toCoindApp ℐ A ε i ≫ Pi.π (coindFam ℐ i) ⟨i, 𝟙 i⟩) := by
    rw [toCoindApp_π]
    infer_instance
  exact mono_of_mono _ (Pi.π (coindFam ℐ i) ⟨i, 𝟙 i⟩)

/-- The morphism into the coinduced system is a monomorphism of systems when each `𝒜ₖ ⟶ ℐₖ`
is. -/
instance mono_toCoind [∀ k : J, Mono (ε k)] : Mono (toCoind ℐ A ε) :=
  mono_of_app_mono _ fun i => mono_toCoindApp ℐ A ε i

/-- Every system of abelian sheaves over `D` admits a monomorphism into a system that is
injective at each stage. -/
theorem exists_mono_stageInjective (A : D.AbelianSystem) :
    ∃ (G : D.AbelianSystem) (α : A ⟶ G), Mono α ∧ ∀ j : J, Injective (G.sheaf j) :=
  ⟨coindSystem fun k => Injective.under (A.sheaf k),
    toCoind _ A fun k => Injective.ι (A.sheaf k),
    mono_toCoind _ A _, fun j => injective_coindSheaf _ j⟩

end AbelianSystem

end SpectralDiagram

end

end
