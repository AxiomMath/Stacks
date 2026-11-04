module

public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Colimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules

/-!
# The colimit half of Stacks 077Z, reduced to exhaustion

Stacks 077Z says that on a system of schemes `X = ({X i}, {f φ})` with every `f φ` flat there is
a cardinal `κ`, depending only on the system, such that every crystal in quasi-coherent modules
on the system is the directed colimit of its `κ`-generated submodules.  The directedness of the
system is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/CrystalsInQuasicoherentModules.lean`.  This file
proves the colimit assertion from the one input it genuinely needs: that every section of the
crystal over an affine open of one of the schemes of the system is a section of one of those
submodules.

## Main definitions

* `Stacks.AlgebraicGeometry.Crystals.Crystal.eval`: evaluation of a crystal at an index of the
  system, as a functor from `CQC(X)` to the modules on `X i`.
* `Stacks.AlgebraicGeometry.Crystals.Subcrystal.toCrystal`: the crystal underlying a submodule
  of a crystal.  Its comparison isomorphism comes from the defining equality
  `α φ ((f φ)^* (G i)) = G i'` of a submodule, read through `Subobject.isoOfMkEq`.
* `Stacks.AlgebraicGeometry.Crystals.Subcrystal.ι`: the inclusion of a submodule of a crystal.
* `Stacks.AlgebraicGeometry.Crystals.cardinalGeneratedSubcrystalFunctor` and
  `Stacks.AlgebraicGeometry.Crystals.cardinalGeneratedSubcrystalCocone`: the diagram of the
  `κ`-generated submodules of a crystal and the canonical cocone from it to the crystal.

## Main results

* `Stacks.AlgebraicGeometry.Crystals.isColimit_of_mono_of_locallySurjective`: a cocone over a
  filtered, essentially small diagram of `𝒪_X`-modules whose legs are monomorphisms and whose
  sections exhaust those of the vertex locally is a colimit cocone.  This is the argument of
  `Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_exists_mem`, stated for an
  arbitrary diagram instead of for the diagram of bounded quasi-coherent subobjects.
* `Stacks.AlgebraicGeometry.Crystals.isColimitOfComponents`: a cocone of crystals is colimiting
  as soon as each of its components is colimiting on the corresponding scheme.  The transition
  isomorphisms cause no trouble because `(f φ)^*` is a left adjoint, so it carries the colimit
  of the component at `i` to a colimit.
* `Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem`:
  **the colimit assertion of Stacks 077Z, from exhaustion.**  If `κ` is infinite and every
  section of the crystal over an affine open of one of the schemes of the system is a section of
  a `κ`-generated submodule, then the crystal is the colimit of its `κ`-generated submodules.

## Implementation notes

`CategoryTheory.Functor.mapCocone` is a `def`, so the vertex of the cocone obtained by evaluating
a cocone of crystals at an index is not *syntactically* the module `c.pt.F i`; a goal mentioning
both is type-correct only after unfolding, and `rw` then refuses to abstract a motive.  The
descent map and the two facts used about it are therefore named —
`Stacks.AlgebraicGeometry.Crystals.descOfComponents`,
`Stacks.AlgebraicGeometry.Crystals.descOfComponents_fac` and
`Stacks.AlgebraicGeometry.Crystals.hom_ext_pullback_component` — with statements written in the
`c.pt.F i` spelling, and the defeq is discharged once, inside their proofs.

## No `@[stacks 077Z]`

No `@[stacks 077Z]` attribute is placed here.  Tag 077Z asserts the existence of a cardinal for
which both the directedness and the colimit hold, and the colimit is proved here only from the
exhaustion hypothesis `hgen`.  That hypothesis is discharged, for `cardinalBound D`, in
`CrystalFamilyTransport.lean`, where the tag's colimit half is stated as
`Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone`.

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration

universe w u

namespace Stacks.AlgebraicGeometry.Crystals

/-! ### A colimit criterion for a diagram of subsheaves -/

/-- **A filtered diagram of subsheaves whose sections exhaust those of its vertex is
colimiting.**  The comparison map out of the colimit is a monomorphism because filtered colimits
of `𝒪_X`-modules are exact, and a monomorphism of `𝒪_X`-modules which is locally surjective on
sections is an isomorphism.  This is the argument of
`Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_exists_mem`, with the diagram of
bounded quasi-coherent subobjects replaced by an arbitrary diagram. -/
def isColimit_of_mono_of_locallySurjective {X : Scheme.{u}} {J : Type w} [Category.{w} J]
    [IsFiltered J] [EssentiallySmall.{u} J] {G : J ⥤ X.Modules} (c : Cocone G)
    (hmono : ∀ j, Mono (c.ι.app j))
    (hsurj : ∀ (U : X.Opens) (s : Γ(c.pt, U)) (x : X), x ∈ U →
      ∃ V : X.Opens, ∃ hVU : V ≤ U, x ∈ V ∧ ∃ j : J,
        c.pt.presheaf.map (homOfLE hVU).op s ∈ Set.range ((c.ι.app j).app V)) :
    IsColimit c := by
  classical
  have hcol : HasColimitsOfShape J X.Modules := hasColimitsOfShape_of_essentiallySmall _ _
  have : IsFiltered (SmallModel J) := IsFiltered.of_equivalence (equivSmallModel _)
  have : HasExactColimitsOfShape J X.Modules :=
    HasExactColimitsOfShape.of_domain_equivalence X.Modules (equivSmallModel _).symm
  have : IsConnected J := IsFiltered.isConnected _
  have : Mono c.ι := NatTrans.mono_of_mono_app _
  have hmcm : Mono (colimMap c.ι) := by
    rw [colimMap_eq]
    exact Functor.map_mono _ _
  have hfac := colimMap_comp_constPointIso c
  have hmc : Mono (colimit.desc G c) := mono_of_comp_iso_eq _ hfac hmcm
  have hloc : ∀ (U : X.Opens) (s : Γ(c.pt, U)) (x : X), x ∈ U →
      ∃ V : X.Opens, ∃ hVU : V ≤ U, x ∈ V ∧
        c.pt.presheaf.map (homOfLE hVU).op s ∈ Set.range ((colimit.desc G c).app V) := by
    intro U s x hx
    obtain ⟨V, hVU, hxV, j, y, hy⟩ := hsurj U s x hx
    refine ⟨V, hVU, hxV, (colimit.ι G j).app V y, ?_⟩
    exact (comp_app_apply _ _ V y).symm.trans
      ((congrArg (fun f : G.obj j ⟶ c.pt => f.app V y) (colimit.ι_desc c j)).trans hy)
  have : IsIso (colimMap c.ι) :=
    isIso_of_comp_iso_eq _ hfac (@isIso_of_mono_of_locallySurjective X _ _ _ hmc hloc)
  exact Cocone.isColimitOfIsIsoColimMapι _

/-! ### Evaluation of a crystal at an index -/

namespace Crystal

variable {D : SchemeSystem.{u}}

/-- The components of a composite of morphisms of crystals are the composites of the
components. -/
@[simp]
theorem comp_hom {M N P : Crystal D} (g : M ⟶ N) (k : N ⟶ P) (i : D.I) :
    (g ≫ k).hom i = g.hom i ≫ k.hom i := rfl

/-- The components of the identity morphism of a crystal are the identities. -/
@[simp]
theorem id_hom (M : Crystal D) (i : D.I) : (𝟙 M : M ⟶ M).hom i = 𝟙 (M.F i) := rfl

/-- **Evaluation at an index of the system**: the functor sending a crystal on the system to its
module on the scheme `X i`. -/
def eval (D : SchemeSystem.{u}) (i : D.I) : Crystal D ⥤ (D.X i).Modules where
  obj M := M.F i
  map g := g.hom i

/-- Evaluation at `i` sends a crystal to its module on `X i`. -/
@[simp]
theorem eval_obj (i : D.I) (M : Crystal D) : (eval D i).obj M = M.F i := rfl

/-- Evaluation at `i` sends a morphism of crystals to its component at `i`. -/
@[simp]
theorem eval_map (i : D.I) {M N : Crystal D} (g : M ⟶ N) : (eval D i).map g = g.hom i := rfl

end Crystal

/-! ### Assembling a colimit of crystals out of its components -/

variable {D : SchemeSystem.{u}} {J : Type w} [Category.{w} J] {G : J ⥤ Crystal D}

/-- The componentwise descent map of a cocone of crystals, assuming that every component of the
cocone `c` is colimiting.  It is named, rather than used inline, so that its type is the one
written here: `CategoryTheory.Functor.mapCocone` is a `def`, so the vertex of the evaluated
cocone is not syntactically `c.pt.F i` and a goal mentioning both cannot be rewritten. -/
def descOfComponents {c : Cocone G} (h : ∀ i : D.I, IsColimit ((Crystal.eval D i).mapCocone c))
    (s : Cocone G) (i : D.I) : c.pt.F i ⟶ s.pt.F i :=
  (h i).desc ((Crystal.eval D i).mapCocone s)

/-- The componentwise descent map factors the legs of the cocone. -/
theorem descOfComponents_fac {c : Cocone G}
    (h : ∀ i : D.I, IsColimit ((Crystal.eval D i).mapCocone c)) (s : Cocone G) (j : J)
    (i : D.I) : (c.ι.app j).hom i ≫ descOfComponents h s i = (s.ι.app j).hom i :=
  (h i).fac ((Crystal.eval D i).mapCocone s) j

/-- The componentwise descent map is the only morphism factoring the legs of the cocone. -/
theorem descOfComponents_uniq {c : Cocone G}
    (h : ∀ i : D.I, IsColimit ((Crystal.eval D i).mapCocone c)) (s : Cocone G) (i : D.I)
    (m : c.pt.F i ⟶ s.pt.F i) (hm : ∀ j : J, (c.ι.app j).hom i ≫ m = (s.ι.app j).hom i) :
    m = descOfComponents h s i :=
  (h i).uniq ((Crystal.eval D i).mapCocone s) m hm

/-- **Two morphisms out of the pullback of a colimiting component agree as soon as they agree
after pulling back the legs of the cocone.**  The pullback functor is a left adjoint, so it
carries the colimit of the component at `i` to a colimit. -/
theorem hom_ext_pullback_component {c : Cocone G} {i : D.I}
    (h : IsColimit ((Crystal.eval D i).mapCocone c)) {Y : Scheme.{u}} (p : Y ⟶ D.X i)
    {W : Y.Modules} {a b : (Scheme.Modules.pullback p).obj (c.pt.F i) ⟶ W}
    (hab : ∀ j : J, (Scheme.Modules.pullback p).map ((c.ι.app j).hom i) ≫ a
      = (Scheme.Modules.pullback p).map ((c.ι.app j).hom i) ≫ b) :
    a = b :=
  (isColimitOfPreserves (Scheme.Modules.pullback p) h).hom_ext hab

/-- **A cocone of crystals is colimiting as soon as all its components are.**  The descent map is
assembled componentwise; its compatibility with the transition isomorphisms is checked after
pulling back the legs of the cocone, which is legitimate because `(f φ)^*` preserves the colimit
of the component at the source index. -/
def isColimitOfComponents (c : Cocone G)
    (h : ∀ i : D.I, IsColimit ((Crystal.eval D i).mapCocone c)) : IsColimit c where
  desc s :=
    { hom := fun i => descOfComponents h s i
      comm := fun φ => by
        refine hom_ext_pullback_component (h (D.j φ).1) (D.f φ) fun j => ?_
        have hc : (Scheme.Modules.pullback (D.f φ)).map ((c.ι.app j).hom (D.j φ).1) ≫
            (c.pt.α φ).hom = ((G.obj j).α φ).hom ≫ (c.ι.app j).hom (D.j φ).2 :=
          ((c.ι.app j).comm φ).symm
        have hs : (Scheme.Modules.pullback (D.f φ)).map ((s.ι.app j).hom (D.j φ).1) ≫
            (s.pt.α φ).hom = ((G.obj j).α φ).hom ≫ (s.ι.app j).hom (D.j φ).2 :=
          ((s.ι.app j).comm φ).symm
        rw [← Category.assoc, hc, Category.assoc, descOfComponents_fac,
          ← Functor.map_comp_assoc, descOfComponents_fac, hs] }
  fac s j := Crystal.Hom.ext (funext fun i => descOfComponents_fac h s j i)
  uniq s m hm := Crystal.Hom.ext (funext fun i =>
    descOfComponents_uniq h s i (m.hom i) fun j =>
      congrArg (fun g : G.obj j ⟶ s.pt => g.hom i) (hm j))

/-! ### The crystal underlying a submodule of a crystal -/

namespace Subcrystal

variable {D : SchemeSystem.{u}} [D.IsFlat] {M : Crystal D}

/-- The morphism `(f φ)^* (G i) ⟶ F i'` whose image is the subsheaf `α φ ((f φ)^* (G i))` of
`F i'`.  For a submodule of a crystal it is a monomorphism onto `G i'`. -/
def transportHom (N : Subcrystal M) (φ : D.Φ) :
    (Scheme.Modules.pullback (D.f φ)).obj ((N.sub (D.j φ).1 : (D.X (D.j φ).1).Modules)) ⟶
      M.F (D.j φ).2 :=
  (Scheme.Modules.pullback (D.f φ)).map (N.sub (D.j φ).1).arrow ≫ (M.α φ).hom

/-- For a flat system the morphism `transportHom` is a monomorphism: `(f φ)^*` is exact, so it
preserves the monomorphism inclusion of `G i`. -/
instance mono_transportHom (N : Subcrystal M) (φ : D.Φ) : Mono (N.transportHom φ) :=
  M.mono_pullbackArrow φ (N.sub (D.j φ).1)

/-- The defining condition of a submodule of a crystal, in the form of an equality of
subobjects of `F i'` with a `Subobject.mk`: the subsheaf cut out by `transportHom` is `G i'`. -/
theorem mk_transportHom (N : Subcrystal M) (φ : D.Φ) :
    Subobject.mk (N.transportHom φ) = N.sub (D.j φ).2 :=
  (M.transport_eq_mk φ (N.sub (D.j φ).1)).symm.trans (N.transport_sub φ)

/-- **The comparison isomorphism of a submodule of a crystal**: the pullback of `G i` along
`f φ` is carried isomorphically onto `G i'` by `α φ`. -/
def transportIso (N : Subcrystal M) (φ : D.Φ) :
    (Scheme.Modules.pullback (D.f φ)).obj ((N.sub (D.j φ).1 : (D.X (D.j φ).1).Modules)) ≅
      ((N.sub (D.j φ).2 : (D.X (D.j φ).2).Modules)) :=
  Subobject.isoOfMkEq _ _ (N.mk_transportHom φ)

/-- The comparison isomorphism of a submodule of a crystal is compatible with the inclusions:
composing it with the inclusion of `G i'` recovers `α φ ∘ (f φ)^*` applied to the inclusion of
`G i`. -/
@[simp]
theorem transportIso_hom_comp_arrow (N : Subcrystal M) (φ : D.Φ) :
    (N.transportIso φ).hom ≫ (N.sub (D.j φ).2).arrow = N.transportHom φ := by
  simp [transportIso, Subobject.ofMkLE]

/-- **The crystal underlying a submodule of a crystal**: the components of the submodule, with
the comparison isomorphisms supplied by the defining condition. -/
def toCrystal (N : Subcrystal M) : Crystal D where
  F i := ((N.sub i : (D.X i).Modules))
  isQuasicoherent := N.isQuasicoherent
  α := N.transportIso

/-- The module of the crystal underlying a submodule, at an index of the system. -/
@[simp]
theorem toCrystal_F (N : Subcrystal M) (i : D.I) :
    N.toCrystal.F i = ((N.sub i : (D.X i).Modules)) := rfl

/-- The comparison isomorphism of the crystal underlying a submodule. -/
@[simp]
theorem toCrystal_α (N : Subcrystal M) (φ : D.Φ) : N.toCrystal.α φ = N.transportIso φ := rfl

/-- **The inclusion of a submodule of a crystal into the crystal.** -/
def ι (N : Subcrystal M) : N.toCrystal ⟶ M where
  hom i := (N.sub i).arrow
  comm φ := N.transportIso_hom_comp_arrow φ

/-- The components of the inclusion of a submodule of a crystal are the inclusions of its
components. -/
@[simp]
theorem ι_hom (N : Subcrystal M) (i : D.I) : (N.ι).hom i = (N.sub i).arrow := rfl

/-- The comparison isomorphisms of two nested submodules are matched by the inclusion of the
smaller into the larger.  This is the compatibility condition making the inclusion a morphism of
crystals; it is checked after composing with the inclusion of the larger submodule into the
crystal, which is a monomorphism. -/
theorem transportIso_hom_comp_ofLE {N N' : Subcrystal M} (h : N ≤ N') (φ : D.Φ) :
    (N.transportIso φ).hom ≫ Subobject.ofLE _ _ (h (D.j φ).2)
      = (Scheme.Modules.pullback (D.f φ)).map (Subobject.ofLE _ _ (h (D.j φ).1))
        ≫ (N'.transportIso φ).hom := by
  refine (cancel_mono (N'.sub (D.j φ).2).arrow).mp ?_
  simp only [Category.assoc, Subobject.ofLE_arrow, transportIso_hom_comp_arrow, transportHom]
  rw [← Functor.map_comp_assoc, Subobject.ofLE_arrow]

/-- **The morphism of crystals induced by a containment of submodules.** -/
def homOfLE' {N N' : Subcrystal M} (h : N ≤ N') : N.toCrystal ⟶ N'.toCrystal where
  hom i := Subobject.ofLE _ _ (h i)
  comm φ := transportIso_hom_comp_ofLE h φ

/-- The components of the morphism induced by a containment of submodules. -/
@[simp]
theorem homOfLE'_hom {N N' : Subcrystal M} (h : N ≤ N') (i : D.I) :
    (homOfLE' h).hom i = Subobject.ofLE _ _ (h i) := rfl

end Subcrystal

/-! ### The diagram of bounded submodules of a crystal -/

variable [D.IsFlat]

/-- **The diagram of the `κ`-generated submodules of a crystal**, as a diagram of crystals. -/
def cardinalGeneratedSubcrystalFunctor (M : Crystal D) (κ : Cardinal.{u}) :
    CardinalGeneratedSubcrystal M κ ⥤ Crystal D where
  obj N := N.1.toCrystal
  map h := Subcrystal.homOfLE' (leOfHom h)
  map_id _ := Crystal.Hom.ext (funext fun _ => Subobject.ofLE_refl _)
  map_comp _ _ := Crystal.Hom.ext (funext fun _ =>
    (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm)

/-- The diagram of `κ`-generated submodules sends a submodule to the crystal it underlies. -/
@[simp]
theorem cardinalGeneratedSubcrystalFunctor_obj (M : Crystal D) (κ : Cardinal.{u})
    (N : CardinalGeneratedSubcrystal M κ) :
    (cardinalGeneratedSubcrystalFunctor M κ).obj N = N.1.toCrystal := rfl

/-- **The canonical cocone from the `κ`-generated submodules of a crystal to the crystal.** -/
def cardinalGeneratedSubcrystalCocone (M : Crystal D) (κ : Cardinal.{u}) :
    Cocone (cardinalGeneratedSubcrystalFunctor M κ) where
  pt := M
  ι :=
    { app := fun N => N.1.ι
      naturality := by
        intro N N' f
        refine Crystal.Hom.ext (funext fun i => ?_)
        change Subobject.ofLE _ _ (leOfHom f i) ≫ (N'.1.sub i).arrow
          = (N.1.sub i).arrow ≫ 𝟙 (M.F i)
        rw [Category.comp_id, Subobject.ofLE_arrow] }

/-- The vertex of the canonical cocone is the crystal itself. -/
@[simp]
theorem cardinalGeneratedSubcrystalCocone_pt (M : Crystal D) (κ : Cardinal.{u}) :
    (cardinalGeneratedSubcrystalCocone M κ).pt = M := rfl

/-- The legs of the canonical cocone are the inclusions of the submodules. -/
@[simp]
theorem cardinalGeneratedSubcrystalCocone_ι_app (M : Crystal D) (κ : Cardinal.{u})
    (N : CardinalGeneratedSubcrystal M κ) :
    (cardinalGeneratedSubcrystalCocone M κ).ι.app N = N.1.ι := rfl

/-- The submodules of a crystal form a `u`-small type: a submodule is determined by its family
of components, there are `u`-many indices, and modules on a scheme are well-powered. -/
instance small_subcrystal (M : Crystal D) : Small.{u} (Subcrystal M) :=
  small_of_injective (f := Subcrystal.sub) fun _ _ h => Subcrystal.ext h

/-! ### The colimit assertion, from exhaustion -/

/-- **The colimit assertion of Stacks 077Z, from exhaustion.**  Let `κ` be an infinite cardinal
and suppose that every section of a crystal `M` over an affine open of one of the schemes of the
system is a section of some `κ`-generated submodule of `M`.  Then the canonical cocone from the
`κ`-generated submodules of `M` to `M` is a colimit cocone.

The hypothesis is about the system of submodules, not about the colimit: it is the exhaustion
half of the tag, the analogue for a system of schemes of the hypothesis `hgen` of
`Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_exists_mem`. -/
def isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem (M : Crystal D) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hgen : ∀ (i : D.I) (U : (D.X i).affineOpens) (s : Γ(M.F i, U.1)),
      ∃ N : CardinalGeneratedSubcrystal M κ, s ∈ Set.range ((N.1.sub i).arrow.app U.1)) :
    IsColimit (cardinalGeneratedSubcrystalCocone M κ) := by
  have : IsFiltered (CardinalGeneratedSubcrystal M κ) :=
    isFiltered_cardinalGeneratedSubcrystal_of_aleph0_le M hκ
  refine isColimitOfComponents _ fun i => ?_
  refine isColimit_of_mono_of_locallySurjective _ (fun _ => Subobject.arrow_mono _) ?_
  intro U s x hx
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ :=
    (D.X i).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (U : Set (D.X i)) from hx) U.isOpen
  have hle : V ≤ U := hVU
  exact ⟨V, hle, hxV, hgen i ⟨V, hVaff⟩ ((M.F i).presheaf.map (homOfLE hle).op s)⟩

end Stacks.AlgebraicGeometry.Crystals

end
