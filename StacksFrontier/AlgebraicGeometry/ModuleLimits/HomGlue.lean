module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Zariski glueing of a morphism of sheaves of modules

Let `M` and `N` be sheaves of modules on a scheme `X` and let `W` be a family of opens covering
`X`.  A morphism `M ⟶ N` is the same thing as a family of morphisms over the members of `W`
agreeing on the overlaps: the *uniqueness* half is `hom_ext_of_app_eq_of_cover`, and the
*existence* half — the glueing — is `exists_hom_app_eq_of_cover`.

Equality of morphisms of sheaves is local and needs only the separatedness half of the sheaf
condition (`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`); constructing a
morphism from local data needs the glueing half.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.homOfSections`: a morphism of sheaves of modules on a
  scheme assembled from its action on sections.  The data is a map `Γ(M, U) → Γ(N, U)` for every
  open `U`, additive, `Γ(X, U)`-homogeneous and compatible with restriction; the resulting
  morphism's `app` is that map, by `rfl`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover`: **Zariski glueing of a
  morphism of sheaves of modules.**  Given a family of opens covering `X` and, over each member,
  a family of maps on sections that is additive, homogeneous, compatible with restriction, and
  such that two members agree on every open contained in both, there is a morphism `M ⟶ N` whose
  action on sections over any open contained in a member of the covering is the given one.
* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover`: two morphisms of sheaves of
  modules agreeing on the sections over every open contained in a member of a covering are equal.
  This is `hom_ext_of_restrict_cover` read on sections.

## Implementation notes

The local data is presented as a family of maps on sections indexed by the opens of `X`
contained in a member of the covering, rather than as a morphism of the restrictions
`Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι`.  The two presentations
carry the same information — the sections of `Scheme.Modules.restrict M f` over `U` are the
sections of `M` over `f ''ᵁ U`, by `rfl` — but the second one does not state the agreement
condition without a transport: for `V ≤ W a` the open `(W a).ι ''ᵁ ((W a).ι ⁻¹ᵁ V)` is equal to
`V` but not definitionally so, so `(φ a).app ((W a).ι ⁻¹ᵁ V)` and `(φ b).app ((W b).ι ⁻¹ᵁ V)`
have types that are only propositionally equal and cannot be compared directly.  The sectionwise
presentation is the one with no transports in it.

The glueing itself is `TopCat.Sheaf.existsUnique_gluing'` for the underlying presheaf of abelian
groups of `N`, applied to the family `U ⊓ W a` for a fixed open `U`.  Additivity, homogeneity and
compatibility with restriction of the glued map are each proved from the *uniqueness* half of
that statement: in each case the candidate value is exhibited and shown to restrict correctly
on each `U ⊓ W a`.

Morphisms of `TopologicalSpace.Opens X` between fixed opens are unique, so the inclusions
produced by `TopCat.Presheaf.IsCompatible` (`TopologicalSpace.Opens.infLELeft` and
`infLERight`) are rewritten to `homOfLE` by `Subsingleton.elim`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Composing two restriction maps of a presheaf on a space -/

/-- Restricting twice along inclusions of opens is restricting once. -/
theorem presheaf_map_homOfLE_comp {Y : TopCat.{u}} (P : TopCat.Presheaf Ab.{u} Y)
    {U V Z : Opens Y} (h₁ : V ≤ U) (h₂ : Z ≤ V) (s : P.obj (op U)) :
    P.map (homOfLE h₂).op (P.map (homOfLE h₁).op s) = P.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 2

section

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### A morphism of sheaves of modules from its action on sections -/

/-- The morphism of sheaves of modules on `X` acting on sections over each open `U` by `g U`.
The hypotheses are exactly that each `g U` is additive and `Γ(X, U)`-homogeneous and that the
family commutes with restriction along inclusions of opens. -/
noncomputable def homOfSections (g : ∀ U : X.Opens, Γ(M, U) → Γ(N, U))
    (hadd : ∀ (U : X.Opens) (m m' : Γ(M, U)), g U (m + m') = g U m + g U m')
    (hsmul : ∀ (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)), g U (r • m) = r • g U m)
    (hres : ∀ (U V : X.Opens) (h : U ≤ V) (m : Γ(M, V)),
      g U (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (g V m)) :
    M ⟶ N :=
  (⟨{ app := fun U => ModuleCat.ofHom
        { toFun := g U.unop
          map_add' := hadd U.unop
          map_smul' := hsmul U.unop }
      naturality := by
        intro U V f
        ext (x : Γ(M, U.unop))
        have h := hres V.unop U.unop (leOfHom f.unop) x
        rw [Subsingleton.elim (homOfLE (leOfHom f.unop)) f.unop] at h
        exact h }⟩ : SheafOfModules.Hom M N)

/-- The sections of `homOfSections g` over `U` act by `g U`. -/
@[simp]
theorem homOfSections_app (g) (hadd) (hsmul) (hres) (U : X.Opens) (m : Γ(M, U)) :
    (homOfSections (M := M) (N := N) g hadd hsmul hres).app U m = g U m :=
  rfl

/-! ### Uniqueness -/

/-- Two morphisms of sheaves of modules on a scheme are equal as soon as they agree on the
sections over every open contained in a member of an open covering.  This is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover` read on sections. -/
theorem hom_ext_of_app_eq_of_cover {ι : Type*} (W : ι → X.Opens) (hW : ∀ x : X, ∃ a, x ∈ W a)
    {φ ψ : M ⟶ N} (h : ∀ (a : ι) (U : X.Opens), U ≤ W a → φ.app U = ψ.app U) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  refine N.isSheaf.section_ext (U := op U) ?_
  intro x hx
  obtain ⟨a, ha⟩ := hW x
  refine ⟨U ⊓ W a, inf_le_left, ⟨hx, ha⟩, ?_⟩
  rw [Hom_app_presheaf_map φ inf_le_left m, Hom_app_presheaf_map ψ inf_le_left m,
    h a (U ⊓ W a) inf_le_right]

/-! ### Existence: the glueing -/

/-- **Zariski glueing of a morphism of sheaves of modules.**  Let `W` be a family of opens
covering the scheme `X` and suppose given, for each member `W a` and each open `U ≤ W a`, a map
`t a U : Γ(M, U) → Γ(N, U)` which is additive, `Γ(X, U)`-homogeneous, compatible with
restriction along inclusions of opens inside `W a`, and such that `t a U` and `t b U` agree
whenever `U` lies in both `W a` and `W b`.  Then there is a morphism `M ⟶ N` acting on the
sections over every open contained in a member of the covering by the given map. -/
theorem exists_hom_app_eq_of_cover {ι : Type u} (W : ι → X.Opens) (hW : ∀ x : X, ∃ a, x ∈ W a)
    (t : ∀ (a : ι) (U : X.Opens), U ≤ W a → Γ(M, U) → Γ(N, U))
    (hadd : ∀ (a : ι) (U : X.Opens) (h : U ≤ W a) (m m' : Γ(M, U)),
      t a U h (m + m') = t a U h m + t a U h m')
    (hsmul : ∀ (a : ι) (U : X.Opens) (h : U ≤ W a) (r : Γ(X, U)) (m : Γ(M, U)),
      t a U h (r • m) = r • t a U h m)
    (hres : ∀ (a : ι) (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ W a) (m : Γ(M, V)),
      t a U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
        = N.presheaf.map (homOfLE hUV).op (t a V hV m))
    (hagree : ∀ (a b : ι) (U : X.Opens) (ha : U ≤ W a) (hb : U ≤ W b) (m : Γ(M, U)),
      t a U ha m = t b U hb m) :
    ∃ φ : M ⟶ N, ∀ (a : ι) (U : X.Opens) (h : U ≤ W a) (m : Γ(M, U)), φ.app U m = t a U h m := by
  classical
  have hcov : ∀ U : X.Opens, U ≤ ⨆ a, U ⊓ W a := by
    intro U x hx
    obtain ⟨a, ha⟩ := hW x
    exact Opens.mem_iSup.mpr ⟨a, hx, ha⟩
  have key : ∀ (U : X.Opens) (m : Γ(M, U)), ∃! s : Γ(N, U), ∀ a : ι,
      N.presheaf.map (homOfLE (inf_le_left : U ⊓ W a ≤ U)).op s
        = t a (U ⊓ W a) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m) := by
    intro U m
    refine TopCat.Sheaf.existsUnique_gluing'
      (F := (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} X))
      (fun a => U ⊓ W a) U (fun a => homOfLE inf_le_left) (hcov U) _ ?_
    intro a b
    change N.presheaf.map _ _ = N.presheaf.map _ _
    rw [Subsingleton.elim (TopologicalSpace.Opens.infLELeft (U ⊓ W a) (U ⊓ W b))
        (homOfLE (inf_le_left : (U ⊓ W a) ⊓ (U ⊓ W b) ≤ U ⊓ W a)),
      Subsingleton.elim (TopologicalSpace.Opens.infLERight (U ⊓ W a) (U ⊓ W b))
        (homOfLE (inf_le_right : (U ⊓ W a) ⊓ (U ⊓ W b) ≤ U ⊓ W b))]
    rw [← hres a _ _ inf_le_left inf_le_right, ← hres b _ _ inf_le_right inf_le_right,
      presheaf_map_homOfLE_comp, presheaf_map_homOfLE_comp]
    exact hagree a b _ _ _ _
  choose g hg hgu using key
  have hlocal : ∀ (a : ι) (U : X.Opens) (h : U ≤ W a) (m : Γ(M, U)), g U m = t a U h m := by
    intro a U h m
    refine (hgu U m _ fun b => ?_).symm
    rw [← hres a _ _ (inf_le_left : U ⊓ W b ≤ U) h]
    exact hagree a b _ _ _ _
  have hadd' : ∀ (U : X.Opens) (m m' : Γ(M, U)), g U (m + m') = g U m + g U m' := by
    intro U m m'
    refine (hgu U _ _ fun a => ?_).symm
    rw [map_add, hg, hg, map_add, hadd]
  have hsmul' : ∀ (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)), g U (r • m) = r • g U m := by
    intro U r m
    refine (hgu U _ _ fun a => ?_).symm
    rw [Scheme.Modules.map_smul, hg, Scheme.Modules.map_smul, hsmul]
  have hres' : ∀ (U V : X.Opens) (h : U ≤ V) (m : Γ(M, V)),
      g U (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (g V m) := by
    intro U V h m
    refine (hgu U _ _ fun a => ?_).symm
    rw [presheaf_map_homOfLE_comp,
      ← presheaf_map_homOfLE_comp (h₁ := (inf_le_left : V ⊓ W a ≤ V))
        (h₂ := inf_le_inf h (le_refl (W a))), hg,
      ← hres a (U ⊓ W a) (V ⊓ W a) (inf_le_inf h (le_refl (W a))) inf_le_right,
      presheaf_map_homOfLE_comp, presheaf_map_homOfLE_comp]
  exact ⟨homOfSections g hadd' hsmul' hres', hlocal⟩

end

end Stacks.AlgebraicGeometry.ModuleLimits

end
