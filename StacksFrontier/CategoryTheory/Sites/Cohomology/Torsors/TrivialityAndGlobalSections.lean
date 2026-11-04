module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.Group
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A torsor is trivial if and only if it has a global section

Fix a site `(C, J)` and a sheaf of (possibly non-commutative) groups `G` on it. A `G`-torsor `F`
is trivial, that is isomorphic as a `G`-torsor to `G` acting on itself by left translation, if
and only if it has a global section: a morphism of presheaves from the terminal presheaf to `F`
(Stacks, Tag 03AI, Lemma 21.4.2). The torsor notions are those of Stacks, Tag 03AH,
Definition 21.4.1.

## Main definitions

* `SheafOfGroups`: a sheaf of groups on `(C, J)`, given section-wise.
* `PseudoTorsor`: a sheaf of sets with a left `G`-action that is simply transitive on every
  nonempty set of sections.
* `PseudoTorsor.Hom`: a morphism of pseudo `G`-torsors.
* `PseudoTorsor.IsTorsor`: a pseudo `G`-torsor that has sections locally.
* `trivialTorsor`: `G` acting on itself by left translation.
* `PseudoTorsor.IsTrivial`: a pseudo `G`-torsor isomorphic to `trivialTorsor G`.
* `GlobalSections`: the morphisms from the terminal presheaf of sets to a presheaf of sets.

## Main results

* `isTrivial_iff_nonempty_globalSections`: a `G`-torsor is trivial if and only if it has a
  global section.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
-/

open CategoryTheory Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A *sheaf of (possibly non-commutative) groups* on the site `(C, J)`: a presheaf of
types that satisfies the sheaf condition, equipped with a group structure on each set of
sections such that the restriction maps are group homomorphisms. -/
@[sga "3 I 2.1.1" "special case", sga "3 IV 4.3.18"]
structure SheafOfGroups (J : GrothendieckTopology C) where
  /-- The underlying presheaf of types. -/
  presheaf : Cᵒᵖ ⥤ Type w
  /-- The sheaf condition. -/
  isSheaf : Presheaf.IsSheaf J presheaf
  /-- The group structure on each set of sections. -/
  group : ∀ U, Group (presheaf.obj U)
  /-- The restriction maps are multiplicative (hence group homomorphisms). -/
  map_mul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g h : presheaf.obj U),
    presheaf.map f (g * h) = presheaf.map f g * presheaf.map f h

attribute [instance] SheafOfGroups.group

/-- A *pseudo `G`-torsor* is a sheaf of sets `F` equipped with a left action `act` of the
sheaf of groups `G` (given section-wise and natural in the object), such that for every
object `U` with `F(U)` nonempty the action of `G(U)` on `F(U)` is simply transitive:
for all `s, t ∈ F(U)` there is a unique `g ∈ G(U)` with `g · s = t`. -/
@[ega "IV 16.5.15" "pseudo-torsor def", sga "3 IV 5.1.0", sga "1 III 5.1", sga "3 III 0.1"]
structure PseudoTorsor (G : SheafOfGroups (C := C) J) where
  /-- The underlying presheaf of sets. -/
  presheaf : Cᵒᵖ ⥤ Type w
  /-- The sheaf condition. -/
  isSheaf : Presheaf.IsSheaf J presheaf
  /-- The left action of sections of `G` on sections of `F`. -/
  act : ∀ U, G.presheaf.obj U → presheaf.obj U → presheaf.obj U
  /-- The identity section acts trivially. -/
  one_act : ∀ U (s : presheaf.obj U), act U 1 s = s
  /-- The action is compatible with multiplication in `G`. -/
  mul_act : ∀ U (g h : G.presheaf.obj U) (s : presheaf.obj U),
    act U (g * h) s = act U g (act U h s)
  /-- The action is natural with respect to the restriction maps, i.e. the action is a
  morphism of sheaves `G × F → F`. -/
  naturality : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.presheaf.obj U) (s : presheaf.obj U),
    presheaf.map f (act U g s) = act V (G.presheaf.map f g) (presheaf.map f s)
  /-- On every nonempty set of sections the action is simply transitive. -/
  simplyTransitive : ∀ U, Nonempty (presheaf.obj U) →
    ∀ s t : presheaf.obj U, ∃! g : G.presheaf.obj U, act U g s = t

variable {G : SheafOfGroups (C := C) J}

/-- A *morphism of pseudo `G`-torsors* `F → F'` is a morphism of presheaves of sets (a natural
transformation) that is compatible with the `G`-actions. -/
@[ext]
structure PseudoTorsor.Hom (F F' : PseudoTorsor (C := C) G) where
  /-- The underlying morphism of presheaves of sets. -/
  hom : F.presheaf ⟶ F'.presheaf
  /-- Compatibility with the `G`-action: `φ(g · s) = g · φ(s)`. -/
  map_act : ∀ U (g : G.presheaf.obj U) (s : F.presheaf.obj U),
    hom.app U (F.act U g s) = F'.act U g (hom.app U s)

/-- An isomorphism of pseudo `G`-torsors is a morphism whose underlying morphism of
presheaves of sets is an isomorphism. -/
def PseudoTorsor.Hom.IsIso {F F' : PseudoTorsor (C := C) G} (φ : F.Hom F') : Prop :=
  CategoryTheory.IsIso φ.hom

/-- A *`G`-torsor* is a pseudo `G`-torsor `F` that has sections locally: for every object `U`
there is a covering `{U_i → U}` of `U` in the site such that `F(U_i)` is nonempty for all `i`. -/
@[ega "IV 16.5.15" "torsor def",
  sga "4½ Arcata 1.6.6" "torsor definition",
  sga "2 XIV 1.4",
  sga "3 IV 5.1.5",
  sga "3 VIB 10.15" "more general",
  sga "4 IV 5.9",
  sga "4½ Sommes_trig 1.2" "more general"]
def PseudoTorsor.IsTorsor (F : PseudoTorsor (C := C) G) : Prop :=
  ∀ U : C, ∃ S ∈ J U, ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, S f → Nonempty (F.presheaf.obj (op V))

/-- The *trivial `G`-torsor* is the sheaf `G` itself, with `G` acting on itself by left
translation `a(g, h) = g * h`. -/
@[ega "IV 16.5.15", sga "4½ Arcata 1.6.6"]
def trivialTorsor (G : SheafOfGroups (C := C) J) : PseudoTorsor (C := C) G where
  presheaf := G.presheaf
  isSheaf := G.isSheaf
  act := fun _ g h => g * h
  one_act := fun U s => one_mul s
  mul_act := fun U g h s => mul_assoc g h s
  naturality := fun f g s => G.map_mul f g s
  simplyTransitive := fun U _ s t => ⟨t * s⁻¹, by group, fun y hy => by rw [← hy]; group⟩

/-- The trivial `G`-torsor is a `G`-torsor. -/
@[ega "IV 16.5.15" "partial"]
theorem trivialTorsor_isTorsor (G : SheafOfGroups (C := C) J) :
    (trivialTorsor G).IsTorsor :=
  fun U => ⟨⊤, J.top_mem U, fun V _ _ => ⟨(1 : G.presheaf.obj (op V))⟩⟩

/-- A pseudo `G`-torsor `F` is *trivial* if it is isomorphic, as a pseudo `G`-torsor, to the
trivial `G`-torsor `trivialTorsor G`. -/
@[ega "IV 16.5.15" "partial"]
def PseudoTorsor.IsTrivial (F : PseudoTorsor (C := C) G) : Prop :=
  ∃ φ : (trivialTorsor G).Hom F, φ.IsIso

/-- The set of global sections `Γ(C, F)` of a presheaf of sets `F`, defined as the set of
morphisms of presheaves from the terminal sheaf `*` (the terminal object of the category
of presheaves of sets) into `F`. -/
@[sga "3 I 1.2",
  sga "3 I 2.3.3.1",
  sga "3 IV 4.1.4.0",
  sga "4 IV 4.3" "special case",
  sga "4 IV 4.3.6" "special case"]
def GlobalSections (F : Cᵒᵖ ⥤ Type w) : Type _ :=
  (⊤_ (Cᵒᵖ ⥤ Type w)) ⟶ F

open CategoryTheory.Limits in
/-- A concrete terminal presheaf: the constant presheaf at `PUnit`. -/
@[ega "0 8.1.10", sga "3 I 1.2"]
def termPresheaf : Cᵒᵖ ⥤ Type w := (Functor.const Cᵒᵖ).obj PUnit

open CategoryTheory.Limits in
/-- `termPresheaf` is a terminal object of `Cᵒᵖ ⥤ Type w`. -/
@[sga "3 I 1.2"]
def termPresheafIsTerminal : IsTerminal (termPresheaf (C := C)) :=
  IsTerminal.ofUniqueHom
    (fun F => { app := fun _ => ↾(fun _ => PUnit.unit), naturality := by intros; rfl })
    (fun F m => by ext; rfl)

open CategoryTheory.Limits in
/-- The chosen terminal object is isomorphic to `termPresheaf`. -/
noncomputable def termIso : (⊤_ (Cᵒᵖ ⥤ Type w)) ≅ termPresheaf (C := C) :=
  terminalIsoIsTerminal termPresheafIsTerminal

/-- The morphism out of `termPresheaf` given by a compatible family of sections `s` of `F`. -/
@[sga "3 I 2.3.3.1" "partial"]
def familyToNat (F : Cᵒᵖ ⥤ Type w) (s : ∀ U, F.obj U)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), F.map f (s U) = s V) :
    termPresheaf (C := C) ⟶ F where
  app U := ↾(fun _ => s U)
  naturality _ _ f := by
    ext
    exact (hnat f).symm

/-- Restriction maps of a sheaf of groups send the identity to the identity. -/
theorem SheafOfGroups.map_one {U V : Cᵒᵖ} (f : U ⟶ V) :
    G.presheaf.map f (1 : G.presheaf.obj U) = 1 := by
  simpa using G.map_mul f (1 : G.presheaf.obj U) 1

/-- A trivial pseudo `G`-torsor has a global section. -/
@[sga "3 IV 5.1.4" "Necessity of a section"]
theorem nonempty_globalSections_of_isTrivial
    (F : PseudoTorsor (C := C) G) (hT : F.IsTrivial) :
    Nonempty (GlobalSections F.presheaf) := by
  obtain ⟨φ, -⟩ := hT
  exact ⟨termIso.hom ≫ familyToNat G.presheaf (fun U => (1 : G.presheaf.obj U))
    (fun f => SheafOfGroups.map_one f) ≫ φ.hom⟩

/-- The torsor morphism `trivialTorsor G → F` attached to a compatible family of sections
`s` of `F`, given on sections over `U` by `g ↦ g · s U`. -/
@[sga "3 IV 5.1.2" "partial"]
def familyToTorsorHom
    (F : PseudoTorsor (C := C) G) (s : ∀ U, F.presheaf.obj U)
    (hcompat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), F.presheaf.map f (s U) = s V) :
    (trivialTorsor G).Hom F where
  hom :=
    { app := fun U => ↾(fun g => F.act U g (s U))
      naturality U V f := by
        ext g
        change F.act V (G.presheaf.map f g) (s V) = F.presheaf.map f (F.act U g (s U))
        rw [F.naturality f g (s U), hcompat f] }
  map_act U g h := F.mul_act U g h (s U)

/-- A pseudo `G`-torsor with a global section is trivial. -/
@[sga "3 IV 5.1.4" "Sufficiency"]
theorem isTrivial_of_nonempty_globalSections
    (F : PseudoTorsor (C := C) G)
    (hσ : Nonempty (GlobalSections F.presheaf)) :
    F.IsTrivial := by
  obtain ⟨σ⟩ := hσ
  let s : ∀ U, F.presheaf.obj U := fun U => (termIso.inv ≫ σ).app U PUnit.unit
  have hcompat {U V : Cᵒᵖ} (f : U ⟶ V) : F.presheaf.map f (s U) = s V :=
    (NatTrans.naturality_apply (termIso.inv ≫ σ) f PUnit.unit).symm
  refine ⟨familyToTorsorHom F s hcompat, ?_⟩
  have (U : Cᵒᵖ) : CategoryTheory.IsIso ((familyToTorsorHom F s hcompat).hom.app U) := by
    rw [isIso_iff_bijective]
    refine ⟨fun g₁ g₂ h => ?_, fun t => ?_⟩
    · obtain ⟨g₀, -, huniq⟩ := F.simplyTransitive U ⟨s U⟩ (s U) (F.act U g₁ (s U))
      exact (huniq g₁ rfl).trans (huniq g₂ h.symm).symm
    · obtain ⟨g₀, hg₀, -⟩ := F.simplyTransitive U ⟨s U⟩ (s U) t
      exact ⟨g₀, hg₀⟩
  exact NatIso.isIso_of_isIso_app _

/-- Let `G` be a sheaf of (possibly non-commutative) groups on a site `C` and `F` a `G`-torsor.
Then `F` is trivial if and only if it has a global section, i.e. `Γ(C, F)` is nonempty
(Stacks, Tag 03AI, Lemma 21.4.2). -/
@[stacks 03AI, sga "3 IV 5.1.4" "partial", sga "3 IV 5.1.5" "(ii)"]
theorem isTrivial_iff_nonempty_globalSections
    (F : PseudoTorsor (C := C) G) (hF : F.IsTorsor) :
    F.IsTrivial ↔ Nonempty (GlobalSections F.presheaf) :=
  (fun _ : F.IsTorsor =>
    ⟨nonempty_globalSections_of_isTrivial F,
      isTrivial_of_nonempty_globalSections F⟩) hF
