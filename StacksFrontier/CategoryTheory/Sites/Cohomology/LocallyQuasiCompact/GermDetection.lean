module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ComparisonSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.OpenRefinement

/-!
# The Zariski comparison inverse image detects germs

Let `S` be a locally quasi-compact Zariski situation, let `X` be an object of its site, let `F` be
a sheaf of sets on the small Zariski site of `X` and let `π_X : Sh(LC_Zar/X) → Sh(X_Zar)` be the
comparison morphism of topoi. This file proves the separatedness statement that both halves of
proper base change for the Zariski comparison (Stacks 0DCU) reduce to:

* if two sections `s, s'` of `F` over an open `W ⊆ X` have the same image in `(π_X^{-1}F)(Z)`,
  for an object `Z` of `LC_Zar/X` factoring through `W`, then `s` and `s'` already agree on an
  open neighbourhood of the image in `X` of every point of `Z`.

An arrow `Z → X` of the site is neither open nor injective, so this cannot be read off from the
sections of `F`; and the two standard proofs are both unavailable at the universes of Stacks
0DCU, where a space in `Type u` carries sheaves of `Type (max (u + 1) v)` with `v` free:

* `TopCat.Presheaf.stalk` is declared for `X : TopCat.{v'}` with `[Category.{v'} C]`, forcing
  `max (u + 1) v = u`;
* Mathlib's local injectivity and local surjectivity of `toSheafify`
  (`CategoryTheory.Presheaf.isLocallyInjective_toSheafify` and its companion) are stated for
  coefficients `Type (max u₂ u₁)` over a site with objects in `Type u₂` and morphisms in
  `Type u₁`, so for the small site `Opens X`, which is `Category.{u, u}`, the only coefficient
  universe they admit is `Type u`.

The proof here uses neither. It uses **left exactness of `π_X^{-1}`**
(`comparisonInverseImage_preservesFiniteLimits`), which holds at all three universes, in the
following way. The agreement locus of `s` and `s'` is the subsheaf `opensEqSheaf F s s'` of the
terminal sheaf, and it is the *equalizer* of `s, s' : opensLeSheaf W ⟶ F`, where `opensLeSheaf W`
is the subsheaf of the terminal sheaf cut out by the open `W`. Being a finite limit, that
equalizer is preserved by `π_X^{-1}`; equalizers in `Sheaf J (Type w)` are created objectwise by
`sheafToPresheaf`, so the hypothesis says exactly that `(π_X^{-1}(opensEqSheaf F s s'))(Z)` is
nonempty. Feeding that section to `exists_opens_comparison_section_eq` produces an open subset of
`X` through which a neighbourhood of the given point maps and on which `s` and `s'` agree.

The subterminal sheaves are built once, from an arbitrary local predicate on opens: a predicate
inherited by smaller opens and satisfied by an open as soon as it is satisfied by the members of
an open cover of it. `opensLeSheaf` and `opensEqSheaf` are the two instances needed, and their
sections are subsingletons, which makes every naturality square and every uniqueness clause in
the limit argument automatic.

## Main definitions

* `Stacks.Topology.opensPredSheaf`: the subsheaf of the terminal sheaf on `Opens T` cut out by a
  local predicate on opens.
* `Stacks.Topology.opensLeSheaf`: the subsheaf of the terminal sheaf given by an open subset.
* `Stacks.Topology.opensEqSheaf`: the agreement subsheaf of two sections of a sheaf.
* `Stacks.Topology.opensLeSheafHom`: a section of `F` over `W` as a morphism
  `opensLeSheaf W ⟶ F`.

## Main results

* `Stacks.Topology.opensEqSheafIsLimit`: the agreement subsheaf is the equalizer of the two
  sections, as morphisms out of `opensLeSheaf W`.
* `comparisonInverseImage_map_comparisonSectionsIso`, in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`: on sections over an open subset of `X`,
  read through `comparisonSectionsIso`, the comparison inverse image of a morphism of sheaves is
  that morphism.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_opens_eq_of_comparison_section_eq`:
  the germ-detection statement above.

These declarations carry no tag.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology

universe u w

section SheafHomElements

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Applying a sheaf morphism at an object and an element respects equality of morphisms. -/
theorem sheafHom_congr {A B : Sheaf J (Type w)} {f g : A ⟶ B} (h : f = g)
    (O : Cᵒᵖ) (a : A.obj.obj O) : f.hom.app O a = g.hom.app O a := by rw [h]

/-- A composite of sheaf morphisms applied to an element. -/
theorem sheafComp_hom_app_apply {A B D : Sheaf J (Type w)} (f : A ⟶ B) (g : B ⟶ D)
    (O : Cᵒᵖ) (a : A.obj.obj O) :
    (f ≫ g).hom.app O a = g.hom.app O (f.hom.app O a) := rfl

/-- A limit fork in `Type w` whose two parallel maps agree at a point of the middle object has
nonempty vertex. -/
theorem nonempty_of_isLimit_fork {A B E : Type w} {f g : A ⟶ B} {j : E ⟶ A}
    (hw : j ≫ f = j ≫ g) (hl : IsLimit (Fork.ofι j hw)) (a : A) (ha : f a = g a) :
    Nonempty E := by
  have hk : (TypeCat.ofHom fun _ : PUnit.{w + 1} => a) ≫ f =
      (TypeCat.ofHom fun _ : PUnit.{w + 1} => a) ≫ g :=
    TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun _ => ha))
  obtain ⟨l, -⟩ := Fork.IsLimit.lift' hl _ hk
  exact ⟨l PUnit.unit⟩

end SheafHomElements

section SubterminalSheaf

variable {T : Type u} [TopologicalSpace T]

/-- Restricting a section of a presheaf on `Opens T` twice is restricting it once. -/
theorem opens_map_op_comp_apply (G : (Opens T)ᵒᵖ ⥤ Type w) {O₁ O₂ O₃ : Opens T}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₁ ⟶ O₃) (s : G.obj (op O₃)) :
    G.map a.op (G.map b.op s) = G.map c.op s := by
  rw [← types_comp_apply (G.map b.op) (G.map a.op), ← G.map_comp, ← op_comp,
    Subsingleton.elim (a ≫ b) c]

/-- The presheaf on `Opens T` whose sections over `O` are the proofs of `P O`, for a predicate
`P` on opens which is inherited by smaller opens. -/
def opensPredPresheaf (P : Opens T → Prop) (hmono : ∀ {O O' : Opens T}, O' ≤ O → P O → P O') :
    (Opens T)ᵒᵖ ⥤ Type w where
  obj O := PULift.{w + 1} (P O.unop)
  map {_ _} i := TypeCat.ofHom fun h => PULift.up (hmono i.unop.le h.down)
  map_id _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun ⟨_⟩ => rfl))
  map_comp _ _ := TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun ⟨_⟩ => rfl))

/-- Sections of `opensPredPresheaf P` are subsingletons. -/
instance opensPredPresheaf_subsingleton (P : Opens T → Prop)
    (hmono : ∀ {O O' : Opens T}, O' ≤ O → P O → P O') (O : (Opens T)ᵒᵖ) :
    Subsingleton ((opensPredPresheaf.{u, w} P hmono).obj O) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- `opensPredPresheaf P` is a sheaf as soon as `P` is a local property of opens: if an open is
covered by opens satisfying `P`, it satisfies `P`. -/
theorem opensPredPresheaf_isSheaf (P : Opens T → Prop)
    (hmono : ∀ {O O' : Opens T}, O' ≤ O → P O → P O')
    (hloc : ∀ (O : Opens T) (ι : Type u) (V : ι → Opens T), (∀ i, V i ≤ O) →
      (∀ x ∈ O, ∃ i, x ∈ V i) → (∀ i, P (V i)) → P O) :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (opensPredPresheaf.{u, w} P hmono) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro O R hR x _
  refine ⟨PULift.up ?_, fun _ _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  refine hloc O {p : Σ V : Opens T, V ⟶ O // R p.2} (fun i => i.1.1)
    (fun i => i.1.2.le) (fun y hy => ?_) (fun i => (x i.1.2 i.2).down)
  obtain ⟨V, f, hf, hyV⟩ := (Opens.mem_grothendieckTopology T).1 hR y hy
  exact ⟨⟨⟨V, f⟩, hf⟩, hyV⟩

/-- The subsheaf of the terminal sheaf cut out by a local predicate on opens. -/
def opensPredSheaf (P : Opens T → Prop) (hmono : ∀ {O O' : Opens T}, O' ≤ O → P O → P O')
    (hloc : ∀ (O : Opens T) (ι : Type u) (V : ι → Opens T), (∀ i, V i ≤ O) →
      (∀ x ∈ O, ∃ i, x ∈ V i) → (∀ i, P (V i)) → P O) :
    Sheaf (Opens.grothendieckTopology T) (Type w) :=
  ⟨opensPredPresheaf.{u, w} P hmono, opensPredPresheaf_isSheaf.{u, w} P hmono hloc⟩

/-- Sections of `opensPredSheaf P` are subsingletons. -/
instance opensPredSheaf_subsingleton (P : Opens T → Prop)
    (hmono : ∀ {O O' : Opens T}, O' ≤ O → P O → P O')
    (hloc : ∀ (O : Opens T) (ι : Type u) (V : ι → Opens T), (∀ i, V i ≤ O) →
      (∀ x ∈ O, ∃ i, x ∈ V i) → (∀ i, P (V i)) → P O) (O : (Opens T)ᵒᵖ) :
    Subsingleton ((opensPredSheaf.{u, w} P hmono hloc).obj.obj O) :=
  opensPredPresheaf_subsingleton.{u, w} P hmono O

/-- The subsheaf of the terminal sheaf given by an open `W`: its sections over `O` are the proofs
of `O ≤ W`, so it is nonempty exactly on the opens contained in `W`. -/
def opensLeSheaf (W : Opens T) : Sheaf (Opens.grothendieckTopology T) (Type w) :=
  opensPredSheaf.{u, w} (fun O => O ≤ W) (fun h h' => h.trans h')
    (fun _ _ V _ hcov hP x hx => by
      obtain ⟨i, hi⟩ := hcov x hx
      exact hP i hi)

/-- The element of `opensLeSheaf W` over an open `O ≤ W`. -/
def opensLeSheafSection {W O : Opens T} (h : O ≤ W) :
    (opensLeSheaf.{u, w} W).obj.obj (op O) :=
  PULift.up h

variable (F : Sheaf (Opens.grothendieckTopology T) (Type w))

/-- A section of `F` over `W` as a morphism from `opensLeSheaf W`. -/
def opensLeSheafHom {W : Opens T} (s : F.obj.obj (op W)) : opensLeSheaf.{u, w} W ⟶ F :=
  ObjectProperty.homMk
    { app _ := TypeCat.ofHom fun h => F.obj.map (homOfLE h.down).op s
      naturality := fun _ _ i => TypeCat.Hom.ext (TypeCat.Fun.ext
        (funext fun h => (opens_map_op_comp_apply F.obj i.unop (homOfLE h.down) _ s).symm)) }

/-- The morphism `opensLeSheafHom F s` sends the section of `opensLeSheaf W` over an open
`O ≤ W` to the restriction of `s` to `O`. -/
@[simp]
theorem opensLeSheafHom_app {W O : Opens T} (s : F.obj.obj (op W)) (h : O ≤ W) :
    (opensLeSheafHom.{u, w} F s).hom.app (op O) (opensLeSheafSection.{u, w} h) =
      F.obj.map (homOfLE h).op s := rfl

/-- The agreement subsheaf of two sections `s, s'` of `F` over `W`: its sections over `O` are the
proofs that `O ≤ W` and that `s` and `s'` have the same restriction to `O`. -/
def opensEqSheaf {W : Opens T} (s s' : F.obj.obj (op W)) :
    Sheaf (Opens.grothendieckTopology T) (Type w) :=
  opensPredSheaf.{u, w}
    (fun O => ∃ h : O ≤ W, F.obj.map (homOfLE h).op s = F.obj.map (homOfLE h).op s')
    (by
      rintro O O' hO' ⟨h, he⟩
      refine ⟨hO'.trans h, ?_⟩
      rw [← opens_map_op_comp_apply F.obj (homOfLE hO') (homOfLE h) _ s,
        ← opens_map_op_comp_apply F.obj (homOfLE hO') (homOfLE h) _ s', he])
    (by
      intro O ι V hVO hcov hP
      have hOW : O ≤ W := fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx
        exact (hP i).1 hi
      refine ⟨hOW, ?_⟩
      have hR : Sieve.ofArrows V (fun i => homOfLE (hVO i)) ∈
          Opens.grothendieckTopology T O := by
        rw [Opens.mem_grothendieckTopology]
        intro x hx
        obtain ⟨i, hi⟩ := hcov x hx
        exact ⟨V i, homOfLE (hVO i),
          ⟨V i, 𝟙 _, homOfLE (hVO i), Presieve.ofArrows.mk i, Category.id_comp _⟩, hi⟩
      refine ((isSheaf_iff_isSheaf_of_type _ _).1 F.property _ hR).isSeparatedFor.ext ?_
      rintro Z f ⟨Z', g, h', ⟨i⟩, rfl⟩
      obtain ⟨hiW, hei⟩ := hP i
      have hZW : Z ≤ W := le_trans (le_trans g.le (hVO i)) hOW
      calc F.obj.map (g ≫ homOfLE (hVO i)).op (F.obj.map (homOfLE hOW).op s)
          = F.obj.map (homOfLE hZW).op s := opens_map_op_comp_apply F.obj _ _ _ s
        _ = F.obj.map g.op (F.obj.map (homOfLE hiW).op s) :=
            (opens_map_op_comp_apply F.obj g (homOfLE hiW) _ s).symm
        _ = F.obj.map g.op (F.obj.map (homOfLE hiW).op s') := by rw [hei]
        _ = F.obj.map (homOfLE hZW).op s' :=
            opens_map_op_comp_apply F.obj g (homOfLE hiW) _ s'
        _ = F.obj.map (g ≫ homOfLE (hVO i)).op (F.obj.map (homOfLE hOW).op s') :=
            (opens_map_op_comp_apply F.obj _ _ _ s').symm)

/-- Any morphism into a sheaf whose sections are subsingletons is given by its action on
sections: naturality is automatic. -/
def opensSubsingletonHom (A B : Sheaf (Opens.grothendieckTopology T) (Type w))
    (hB : ∀ O : (Opens T)ᵒᵖ, Subsingleton (B.obj.obj O))
    (h : ∀ O : (Opens T)ᵒᵖ, A.obj.obj O → B.obj.obj O) : A ⟶ B :=
  ObjectProperty.homMk
    { app O := TypeCat.ofHom (h O)
      naturality := fun _ O' _ => TypeCat.Hom.ext (TypeCat.Fun.ext
        (funext fun _ => (hB O').elim _ _)) }

/-- Two morphisms into a sheaf whose sections are subsingletons are equal. -/
theorem opensSubsingleton_hom_ext {A B : Sheaf (Opens.grothendieckTopology T) (Type w)}
    (hB : ∀ O : (Opens T)ᵒᵖ, Subsingleton (B.obj.obj O)) (f g : A ⟶ B) : f = g := by
  ext O a
  exact (hB O).elim _ _

/-- Sections of `opensLeSheaf` are subsingletons. -/
theorem opensLeSheaf_subsingleton (W : Opens T) (O : (Opens T)ᵒᵖ) :
    Subsingleton ((opensLeSheaf.{u, w} W).obj.obj O) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- Sections of `opensEqSheaf` are subsingletons. -/
theorem opensEqSheaf_subsingleton {W : Opens T} (s s' : F.obj.obj (op W)) (O : (Opens T)ᵒᵖ) :
    Subsingleton ((opensEqSheaf.{u, w} F s s').obj.obj O) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The inclusion of the agreement subsheaf into the open-subset subsheaf. -/
def opensEqSheafι {W : Opens T} (s s' : F.obj.obj (op W)) :
    opensEqSheaf.{u, w} F s s' ⟶ opensLeSheaf.{u, w} W :=
  opensSubsingletonHom.{u, w} _ _ (opensLeSheaf_subsingleton.{u, w} W)
    (fun _ a => PULift.up a.down.1)

/-- The two section morphisms agree on the agreement subsheaf. -/
theorem opensEqSheafι_comp_eq {W : Opens T} (s s' : F.obj.obj (op W)) :
    opensEqSheafι.{u, w} F s s' ≫ opensLeSheafHom.{u, w} F s =
      opensEqSheafι.{u, w} F s s' ≫ opensLeSheafHom.{u, w} F s' := by
  ext O a
  exact a.down.2

/-- **The agreement subsheaf is the equalizer of two sections.** The two sections of `F` over `W`,
viewed as morphisms out of `opensLeSheaf W`, are equalized by the inclusion of the agreement
subsheaf, and that fork is a limit: a section of any sheaf over `O` whose image in
`opensLeSheaf W` is equalized by them witnesses `O ≤ W` and the agreement of `s` and `s'`
over `O`. -/
def opensEqSheafIsLimit {W : Opens T} (s s' : F.obj.obj (op W)) :
    IsLimit (Fork.ofι (opensEqSheafι.{u, w} F s s') (opensEqSheafι_comp_eq.{u, w} F s s')) :=
  Fork.IsLimit.mk _
    (fun c => opensSubsingletonHom.{u, w} c.pt (opensEqSheaf.{u, w} F s s')
      (opensEqSheaf_subsingleton.{u, w} F s s')
      (fun O z => PULift.up ⟨(c.ι.hom.app O z).down, by
        have h₁ := sheafHom_congr c.condition O z
        rwa [sheafComp_hom_app_apply, sheafComp_hom_app_apply] at h₁⟩))
    (fun _ => opensSubsingleton_hom_ext.{u, w} (opensLeSheaf_subsingleton.{u, w} W) _ _)
    (fun _ _ _ => opensSubsingleton_hom_ext.{u, w}
      (opensEqSheaf_subsingleton.{u, w} F s s') _ _)

/-- The sections of the agreement subsheaf, unfolded. -/
theorem opensEqSheaf_down {W O : Opens T} (s s' : F.obj.obj (op W))
    (a : (opensEqSheaf.{u, w} F s s').obj.obj (op O)) :
    ∃ h : O ≤ W, F.obj.map (homOfLE h).op s = F.obj.map (homOfLE h).op s' := a.down

end SubterminalSheaf

end Stacks.Topology

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w' v

open Stacks.Topology

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w'} S₀ Bound)

/-- The underlying map of a composite of morphisms of the site, applied to a point. -/
private theorem site_comp_apply {A B C : S.category} (c : A ⟶ B) (b : B ⟶ C) (x : A.obj) :
    ((c ≫ b : A ⟶ C) : A.obj → C.obj) x = (b : B.obj → C.obj) ((c : A.obj → B.obj) x) := rfl

/-- The comparison inverse image of a morphism of sheaves, read on the sections over an open
subset of `X` through `comparisonSectionsIso`: it is the morphism itself. This is naturality of
the unit of the comparison adjunction. -/
theorem comparisonInverseImage_map_comparisonSectionsIso (X : S.category)
    {G H : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))} (φ : G ⟶ H)
    (U : Opens X.obj) (y : G.obj.obj (Opposite.op U)) :
    ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).map φ).hom.app
        (Opposite.op ((S.opensToSlice X).1.obj U))
        ((comparisonSectionsIso.{u, w', max (u + 1) v} S X G U).hom y) =
      (comparisonSectionsIso.{u, w', max (u + 1) v} S X H U).hom
        (φ.hom.app (Opposite.op U) y) := by
  exact (sheafHom_congr
    ((S.comparisonAdjunction.{u, w', max (u + 1) v} X).unit.naturality φ) (Opposite.op U) y).symm

/-- The comparison inverse image of the morphism `opensLeSheafHom F r`, evaluated at `Z` on the
section of `π_X^{-1}(opensLeSheaf W)` pulled back along `ψ`, is the pullback along `ψ` of the
section of `π_X^{-1}F` corresponding to `r`. -/
theorem comparisonInverseImage_map_opensLeSheafHom (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over X} {W : Opens X.obj} (ψ : Z ⟶ (S.opensToSlice X).1.obj W)
    (r : F.obj.obj (Opposite.op W)) :
    ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).map
          (opensLeSheafHom.{u, max (u + 1) v} F r)).hom.app (Opposite.op Z)
        (((S.comparisonInverseImage.{u, w', max (u + 1) v} X).obj
            (opensLeSheaf.{u, max (u + 1) v} W)).obj.map ψ.op
          ((comparisonSectionsIso.{u, w', max (u + 1) v} S X
              (opensLeSheaf.{u, max (u + 1) v} W) W).hom
            (opensLeSheafSection.{u, max (u + 1) v} (le_refl W)))) =
      ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).obj F).obj.map ψ.op
        ((comparisonSectionsIso.{u, w', max (u + 1) v} S X F W).hom r) := by
  have h₁ := types_congr_hom
    (((S.comparisonInverseImage.{u, w', max (u + 1) v} X).map
      (opensLeSheafHom.{u, max (u + 1) v} F r)).hom.naturality ψ.op)
    ((comparisonSectionsIso.{u, w', max (u + 1) v} S X
        (opensLeSheaf.{u, max (u + 1) v} W) W).hom
      (opensLeSheafSection.{u, max (u + 1) v} (le_refl W)))
  rw [types_comp_apply, types_comp_apply,
    comparisonInverseImage_map_comparisonSectionsIso.{u, w', v} S X
      (opensLeSheafHom.{u, max (u + 1) v} F r) W
      (opensLeSheafSection.{u, max (u + 1) v} (le_refl W)),
    opensLeSheafHom_app] at h₁
  rw [h₁, Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, F.obj.map_id, types_id_apply]

/-- **Lemma C: the comparison inverse image detects germs.** Let `F` be a sheaf on the small
Zariski site of `X`, let `Z` be an object of `LC_Zar/X` which factors through an open subset `W`
of `X` by `ψ`, and let `s, s'` be sections of `F` over `W`. If the two sections of `π_X^{-1}F`
over `Z` obtained by pulling `s` and `s'` back along `ψ` agree, then `s` and `s'` already agree
on an open neighbourhood of the image of every point of `Z`. -/
theorem exists_opens_eq_of_comparison_section_eq (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over X} {W : Opens X.obj} (ψ : Z ⟶ (S.opensToSlice X).1.obj W)
    (s s' : F.obj.obj (Opposite.op W)) (p : Z.left.obj)
    (hps : ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).obj F).obj.map ψ.op
        ((comparisonSectionsIso.{u, w', max (u + 1) v} S X F W).hom s) =
      ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).obj F).obj.map ψ.op
        ((comparisonSectionsIso.{u, w', max (u + 1) v} S X F W).hom s')) :
    ∃ (W' : Opens X.obj) (_ : (Z.hom : Z.left.obj → X.obj) p ∈ W') (h : W' ≤ W),
      F.obj.map (homOfLE h).op s = F.obj.map (homOfLE h).op s' := by
  classical
  let Φ : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)) ⥤
      Type (max (u + 1) v) :=
    S.comparisonInverseImage.{u, w', max (u + 1) v} X ⋙
      sheafToPresheaf (S.zariskiTopology.over X) (Type (max (u + 1) v)) ⋙
      (evaluation (Over X)ᵒᵖ (Type (max (u + 1) v))).obj (Opposite.op Z)
  have hinv : PreservesFiniteLimits (S.comparisonInverseImage.{u, w', max (u + 1) v} X) :=
    comparisonInverseImage_preservesFiniteLimits.{u, w', max (u + 1) v} S X
  have hΦ : PreservesFiniteLimits Φ := comp_preservesFiniteLimits _ _
  have hfork := isLimitForkMapOfIsLimit Φ (opensEqSheafι_comp_eq.{u, max (u + 1) v} F s s')
    (opensEqSheafIsLimit.{u, max (u + 1) v} F s s')
  have hΦmap : ∀ {G H : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))}
      (φ : G ⟶ H), Φ.map φ =
        ((S.comparisonInverseImage.{u, w', max (u + 1) v} X).map φ).hom.app (Opposite.op Z) :=
    fun _ => rfl
  obtain ⟨a⟩ := nonempty_of_isLimit_fork _ hfork
    (((S.comparisonInverseImage.{u, w', max (u + 1) v} X).obj
        (opensLeSheaf.{u, max (u + 1) v} W)).obj.map ψ.op
      ((comparisonSectionsIso.{u, w', max (u + 1) v} S X
          (opensLeSheaf.{u, max (u + 1) v} W) W).hom
        (opensLeSheafSection.{u, max (u + 1) v} (le_refl W))))
    (by
      rw [hΦmap, hΦmap, comparisonInverseImage_map_opensLeSheafHom.{u, w', v} S X F ψ s,
        comparisonInverseImage_map_opensLeSheafHom.{u, w', v} S X F ψ s']
      exact hps)
  obtain ⟨V, hpV, W', c, b, -⟩ :=
    exists_opens_comparison_section_eq.{u, w', v} S X
      (opensEqSheaf.{u, max (u + 1) v} F s s') a p
  obtain ⟨hW'W, heq⟩ := opensEqSheaf_down.{u, max (u + 1) v} F s s'
    ((comparisonSectionsIso.{u, w', max (u + 1) v} S X
        (opensEqSheaf.{u, max (u + 1) v} F s s') W').inv b)
  refine ⟨W', ?_, hW'W, heq⟩
  obtain ⟨q, hq⟩ : ∃ q, ((((S.opensToSlice Z.left).1.obj V).hom) :
      (((S.opensToSlice Z.left).1.obj V).left).obj → Z.left.obj) q = p := by
    rwa [← Set.mem_range, ((S.opensToSlice Z.left).2 V).2]
  have hw := congrArg (fun k : ((S.opensToSlice Z.left).1.obj V).left ⟶ X =>
    (k : (((S.opensToSlice Z.left).1.obj V).left).obj → X.obj) q) (Over.w c)
  simp only [Over.mk_hom, site_comp_apply] at hw
  rw [hq] at hw
  have hmem : ((((S.opensToSlice X).1.obj W').hom) :
      (((S.opensToSlice X).1.obj W').left).obj → X.obj)
      ((c.left : (((S.opensToSlice Z.left).1.obj V).left).obj →
        (((S.opensToSlice X).1.obj W').left).obj) q) ∈
      Set.range ((((S.opensToSlice X).1.obj W').hom) :
        (((S.opensToSlice X).1.obj W').left).obj → X.obj) := Set.mem_range_self _
  rw [((S.opensToSlice X).2 W').2] at hmem
  rwa [← hw]

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
