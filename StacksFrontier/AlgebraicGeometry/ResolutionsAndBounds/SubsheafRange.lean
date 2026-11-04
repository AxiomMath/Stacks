module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubsheafGluing

/-!
# Submodules of a module on a scheme from monomorphisms, and from an open subscheme

Two sources of submodules of an `𝒪_X`-module `M` in the sense of `SheafOfModules.Submodule`:

* a monomorphism `a : A ⟶ M` has a *range*, the family of submodules of sections of `M` that are
  in the image of `a`. Its membership condition is local precisely because `a` is a
  monomorphism: the local preimages are unique, so they glue.
* a submodule `N` of the restriction `M.restrict V.ι` of `M` to an open `V` has a *push*, the
  family of sections of `M` whose restriction to the part of their domain of definition lying in
  `V` is a section of `N`. It constrains a section only over `V`.

Together with the sectionwise intersection
`Stacks.AlgebraicGeometry.Subsheaf.inter` these give the gluing of a submodule across a
two-element open cover `X = W ∪ V`: the glued submodule is `inter B (push V N)` for `B` the
prescription on `W` and `N` the prescription on `V`, and
`Stacks.AlgebraicGeometry.Subsheaf.inter_obj_of_le_left` and
`Stacks.AlgebraicGeometry.Subsheaf.inter_obj_eq_right` identify its sections on each side.

## Main definitions

* `Stacks.AlgebraicGeometry.Subsheaf.rangeObj` and `Stacks.AlgebraicGeometry.Subsheaf.ofMono`:
  the range of a monomorphism of `𝒪_X`-modules, sectionwise and as a submodule.
* `Stacks.AlgebraicGeometry.Subsheaf.pushObj` and `Stacks.AlgebraicGeometry.Subsheaf.push`: the
  push of a submodule of `M.restrict V.ι` to a submodule of `M`.
* `Stacks.AlgebraicGeometry.Subsheaf.pre` is the preimage of an open of `X` in an open
  subscheme.
* `Stacks.AlgebraicGeometry.Subsheaf.mod` and `Stacks.AlgebraicGeometry.Subsheaf.modι`: the
  `𝒪_X`-module underlying a submodule of `M`, and its inclusion into `M`.
* `Stacks.AlgebraicGeometry.Subsheaf.inclusion`: the inclusion of one submodule of `M` into
  another containing it.
* `Stacks.AlgebraicGeometry.Subsheaf.liftOfMono` and
  `Stacks.AlgebraicGeometry.Subsheaf.isoOfMono`: the factorization of a monomorphism through its
  range, and the resulting isomorphism of its source with its range.
* `Stacks.AlgebraicGeometry.Subsheaf.pushRestrictIso`: the identification of a submodule of
  `M.restrict V.ι` with the restriction to `V` of its push.
* `Stacks.AlgebraicGeometry.Subsheaf.le_push_of_le_image` and
  `Stacks.AlgebraicGeometry.Subsheaf.push_le_of_le_image`: the two containments that the gluing
  asks for, from the comparison of `N` with `B` over the opens of `V`.

## Main results

* `Stacks.AlgebraicGeometry.Subsheaf.eq_of_res_eq` and
  `Stacks.AlgebraicGeometry.Subsheaf.exists_glue`: separatedness and gluing of sections of an
  `𝒪_X`-module, in the form used throughout.
* `Stacks.AlgebraicGeometry.Subsheaf.mem_rangeObj_of_local`: being in the range of a
  monomorphism is a local condition.
* `Stacks.AlgebraicGeometry.Subsheaf.isIso_of_bijective_app`: a morphism of `𝒪_X`-modules which
  is bijective on sections over every open is an isomorphism.
* `Stacks.AlgebraicGeometry.Subsheaf.mem_push_iff`: the sections of the push.
* `Stacks.AlgebraicGeometry.Subsheaf.isIso_restrict_inclusion`: two submodules of `M` which agree
  on the opens contained in `W` have isomorphic restrictions to `W`. With the locality of finite
  type and of quasi-coherence on an open cover this is what transports those properties across a
  gluing.
* `Stacks.AlgebraicGeometry.Subsheaf.isoOfMono_hom_comp`: the isomorphism of a monomorphism with
  its range respects the inclusions into the target, so a subobject of `M` and the submodule of
  `M` given by its range are the same subobject.

## Implementation notes

The sections of `M.restrict V.ι` over an open `W` of `V` are *equal* to the sections of `M` over
`V.ι ''ᵁ W`, but the module structures are over the two rings `Γ(V.toScheme, W)` and
`Γ(X, V.ι ''ᵁ W)`, which differ by the ring isomorphism `V.ι.appIso W`. `smul_restrict_eq`
identifies the two actions, and is the only place where that comparison is made.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Subsheaf

variable {X : Scheme.{u}} {M A : X.Modules}

/-! ### Sections of a module on a scheme -/

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections. -/
lemma app_res (a : A ⟶ M) {T T' : X.Opens} (h : T' ≤ T) (w : Γ(A, T)) :
    a.app T' (res A h w) = res M h (a.app T w) := by
  have h1 := NatTrans.naturality a.mapPresheaf (homOfLE h).op
  have h2 := congr($h1 w)
  simp only [comp_apply, Scheme.Modules.mapPresheaf_app] at h2
  exact h2

/-- Restriction of sections is semilinear for restriction of scalars. -/
lemma res_smul (M : X.Modules) {T T' : X.Opens} (h : T' ≤ T) (r : Γ(X, T)) (s : Γ(M, T)) :
    res M h (r • s) = X.presheaf.map (homOfLE h).op r • res M h s :=
  M.map_smul _ r s

/-- A monomorphism of `𝒪_X`-modules is injective on sections over every open. -/
lemma injective_app (a : A ⟶ M) [Mono a] (T : X.Opens) : Function.Injective (a.app T) := by
  have h1 : Mono ((Scheme.Modules.toPresheafOfModules X).map a) :=
    (Scheme.Modules.toPresheafOfModules X).map_mono a
  have h2 : Mono a.val := h1
  exact PresheafOfModules.injective_of_mono a.val (op T)

/-- An `𝒪_X`-module as a sheaf of abelian groups, which is the form in which the gluing of
sections is available. -/
noncomputable def abSheaf (M : X.Modules) : TopCat.Sheaf Ab (X : TopCat.{u}) :=
  ⟨M.presheaf, M.isSheaf⟩

/-- **Separatedness.** Two sections of an `𝒪_X`-module over an open covered by a family of opens
which agree on each member of the family are equal. -/
lemma eq_of_res_eq (M : X.Modules) {T : X.Opens} {ι : Type u} (U : ι → X.Opens)
    (hU : T ≤ iSup U) (hUT : ∀ i, U i ≤ T) {s t : Γ(M, T)}
    (h : ∀ i, res M (hUT i) s = res M (hUT i) t) : s = t := by
  obtain ⟨_, _, huniq⟩ := (abSheaf M).existsUnique_gluing' U T (fun i => homOfLE (hUT i)) hU
    (fun i => res M (hUT i) s) (by
      intro i j
      show res M (inf_le_left : U i ⊓ U j ≤ U i) (res M (hUT i) s) =
        res M (inf_le_right : U i ⊓ U j ≤ U j) (res M (hUT j) s)
      rw [res_res, res_res])
  rw [huniq s fun _ => rfl, huniq t fun i => (h i).symm]

/-- **Gluing.** A compatible family of sections of an `𝒪_X`-module over a family of opens covering
`T` comes from a section over `T`. -/
lemma exists_glue (A : X.Modules) {T : X.Opens} {ι : Type u} (U : ι → X.Opens)
    (hU : T ≤ iSup U) (hUT : ∀ i, U i ≤ T) (sf : ∀ i, Γ(A, U i))
    (cpt : ∀ i j, res A (inf_le_left : U i ⊓ U j ≤ U i) (sf i) =
      res A (inf_le_right : U i ⊓ U j ≤ U j) (sf j)) :
    ∃ w : Γ(A, T), ∀ i, res A (hUT i) w = sf i := by
  obtain ⟨g, hg, -⟩ := (abSheaf A).existsUnique_gluing' U T (fun i => homOfLE (hUT i)) hU sf
    (fun i j => cpt i j)
  exact ⟨g, hg⟩

/-- A morphism of `𝒪_X`-modules which is bijective on sections over every open is an
isomorphism. -/
lemma isIso_of_bijective_app (a : A ⟶ M) (h : ∀ T : X.Opens, Function.Bijective (a.app T)) :
    IsIso a := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h T

/-! ### The range of a monomorphism -/

/-- The sections of `M` over `T` which are in the image of `a`. -/
noncomputable def rangeObj (a : A ⟶ M) (T : X.Opens) : Submodule Γ(X, T) Γ(M, T) where
  carrier := Set.range (a.app T)
  add_mem' := by
    rintro x y ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r x ⟨w, rfl⟩
    exact ⟨r • w, a.app_smul r w⟩

/-- Membership in the range of a morphism. -/
lemma mem_rangeObj {a : A ⟶ M} {T : X.Opens} {s : Γ(M, T)} :
    s ∈ rangeObj a T ↔ ∃ w, a.app T w = s := Iff.rfl

/-- Being in the range of a *monomorphism* is a local condition: the local preimages are unique,
hence glue. -/
lemma mem_rangeObj_of_local (a : A ⟶ M) [Mono a] {T : X.Opens} (s : Γ(M, T))
    (h : ∀ x ∈ T, ∃ (P : X.Opens) (hP : P ≤ T), x ∈ P ∧ res M hP s ∈ rangeObj a P) :
    s ∈ rangeObj a T := by
  classical
  choose! P hPle hxP hmem using h
  let ι : Type u := {x : ↥X // x ∈ T}
  let U : ι → X.Opens := fun i => P i.1
  have hUT : ∀ i, U i ≤ T := fun i => hPle i.1 i.2
  have hU : T ≤ iSup U := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxP x hx⟩
  have hres : ∀ i, res M (hUT i) s ∈ rangeObj a (U i) := fun i => hmem i.1 i.2
  choose sf hsf using hres
  have cpt : ∀ i j, res A (inf_le_left : U i ⊓ U j ≤ U i) (sf i) =
      res A (inf_le_right : U i ⊓ U j ≤ U j) (sf j) := by
    intro i j
    refine injective_app a (U i ⊓ U j) ?_
    rw [app_res, app_res, hsf i, hsf j]
    rw [res_res, res_res]
  obtain ⟨w, hw⟩ := exists_glue A U hU hUT sf cpt
  refine mem_rangeObj.mpr ⟨w, ?_⟩
  refine eq_of_res_eq M U hU hUT fun i => ?_
  rw [← app_res, hw, hsf i]

/-- The **range** of a monomorphism of `𝒪_X`-modules, as a submodule of its target. -/
noncomputable def ofMono (a : A ⟶ M) [Mono a] : SheafOfModules.Submodule M where
  obj T := rangeObj a T.unop
  map {T T'} f s hs := by
    obtain ⟨w, hw⟩ := mem_rangeObj.mp hs
    refine mem_rangeObj.mpr ⟨res A (leOfHom f.unop) w, ?_⟩
    rw [app_res, hw]
    rfl
  isSheaf := by
    intro T s hs
    rw [Opens.mem_grothendieckTopology] at hs
    refine mem_rangeObj_of_local a s fun x hx => ?_
    obtain ⟨Q, f, hf, hxQ⟩ := hs x hx
    exact ⟨Q, leOfHom f, hxQ, hf⟩

/-- The sections of the range of a monomorphism. -/
lemma ofMono_obj (a : A ⟶ M) [Mono a] (T : X.Opens) : (ofMono a).obj (op T) = rangeObj a T := rfl

/-! ### Pushing a submodule of a restriction -/

variable (M) in
/-- The action of `Γ(X, f ''ᵁ W)` on the sections of `M` over `f ''ᵁ W` is the action of
`Γ(Y, W)` on the sections of `M.restrict f` over `W`, transported along the ring isomorphism
`f.appIso W`. -/
lemma smul_restrict_eq {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (W : Y.Opens)
    (r : Γ(Y, W)) : ((M.restrict f).smul r) = M.smul ((f.appIso W).inv r) := by
  have h := Scheme.Modules.smul_restrictAppIso_hom f M W r
  rw [Scheme.Modules.restrictAppIso] at h
  simp only [Iso.refl_hom] at h
  exact h

/-- A submodule of `M.restrict V.ι` is stable under the action of the sections of `𝒪_X`. -/
lemma smul_mem_restrict {V : X.Opens} (N : SheafOfModules.Submodule (M.restrict V.ι))
    (W : V.toScheme.Opens) (r : Γ(X, V.ι ''ᵁ W)) {x : Γ(M, V.ι ''ᵁ W)}
    (hx : x ∈ N.obj (op W)) : r • x ∈ N.obj (op W) := by
  have h1 := (N.obj (op W)).smul_mem ((V.ι.appIso W).hom r) hx
  have h2 : ((M.restrict V.ι).smul ((V.ι.appIso W).hom r)) = M.smul r := by
    rw [smul_restrict_eq]
    congr 1
    exact congr($((V.ι.appIso W).hom_inv_id) r)
  have h3 : ((M.restrict V.ι).smul ((V.ι.appIso W).hom r)).hom x = r • x := by
    rw [h2]; rfl
  rw [← h3]
  exact h1

/-- The preimage of an open of `X` in the open subscheme `V`. Stated with the target type
`V.toScheme.Opens` so that the two spellings of the underlying space of the open subscheme do not
proliferate. -/
def pre (V T : X.Opens) : V.toScheme.Opens := V.ι ⁻¹ᵁ T

/-- The image of the preimage is contained in the original open. -/
lemma image_pre_le (V T : X.Opens) : V.ι ''ᵁ pre V T ≤ T := V.ι.image_preimage_le T

/-- Taking preimages is monotone. -/
lemma pre_mono (V : X.Opens) {T T' : X.Opens} (h : T' ≤ T) : pre V T' ≤ pre V T := fun _ hx => h hx

/-- An open contained in `V` is the image of its preimage in the open subscheme `V`. -/
lemma image_pre_eq (V : X.Opens) {T : X.Opens} (h : T ≤ V) : V.ι ''ᵁ pre V T = T := by
  apply Opens.ext
  ext x
  refine ⟨?_, fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

/-- The sections of `M` over `T` whose restriction to the part of `T` inside `V` is a section
of `N`. -/
noncomputable def pushObj (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι))
    (T : X.Opens) : Submodule Γ(X, T) Γ(M, T) where
  carrier := {s | res M (image_pre_le V T) s ∈ N.obj (op (pre V T))}
  add_mem' {x y} hx hy := by
    change res M (image_pre_le V T) (x + y) ∈ N.obj (op (pre V T))
    rw [show res M (image_pre_le V T) (x + y) =
      res M (image_pre_le V T) x + res M (image_pre_le V T) y from map_add _ _ _]
    exact (N.obj (op (pre V T))).add_mem hx hy
  zero_mem' := by
    change res M (image_pre_le V T) (0 : Γ(M, T)) ∈ N.obj (op (pre V T))
    rw [show res M (image_pre_le V T) (0 : Γ(M, T)) = 0 from map_zero _]
    exact (N.obj (op (pre V T))).zero_mem
  smul_mem' r x hx := by
    change res M (image_pre_le V T) (r • x) ∈ N.obj (op (pre V T))
    rw [res_smul]
    exact smul_mem_restrict N (pre V T) _ hx

/-- Membership in `pushObj`. -/
lemma mem_pushObj {V : X.Opens} {N : SheafOfModules.Submodule (M.restrict V.ι)} {T : X.Opens}
    {s : Γ(M, T)} :
    s ∈ pushObj V N T ↔ res M (image_pre_le V T) s ∈ N.obj (op (pre V T)) := Iff.rfl

/-- Restriction of sections of `M.restrict V.ι` is restriction of sections of `M`. -/
lemma res_restrict_eq {V : X.Opens} {W W' : V.toScheme.Opens} (h : W' ≤ W)
    (s : Γ(M, V.ι ''ᵁ W)) :
    res (M.restrict V.ι) h s = res M (V.ι.image_mono h) s := rfl

/-- `pushObj` is stable under restriction of sections. -/
lemma mem_pushObj_res (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι))
    {T T' : X.Opens} (h : T' ≤ T) {s : Γ(M, T)} (hs : s ∈ pushObj V N T) :
    res M h s ∈ pushObj V N T' := by
  refine mem_pushObj.mpr ?_
  have h2 : res M (V.ι.image_mono (pre_mono V h)) (res M (image_pre_le V T) s) ∈
      N.obj (op (pre V T')) := mem_of_le N (pre_mono V h) (mem_pushObj.mp hs)
  rw [res_res] at h2
  rw [res_res]
  exact h2

/-- Membership in `pushObj` is a local condition. -/
lemma mem_pushObj_of_local (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι))
    {T : X.Opens} (s : Γ(M, T))
    (h : ∀ x ∈ T, ∃ (P : X.Opens) (hP : P ≤ T), x ∈ P ∧ res M hP s ∈ pushObj V N P) :
    s ∈ pushObj V N T := by
  refine mem_pushObj.mpr (mem_of_local N _ fun y hy => ?_)
  obtain ⟨Q, hQ, hyQ, hmem⟩ := h y.1 hy
  refine ⟨pre V (Q ⊓ T), pre_mono V inf_le_right, ⟨hyQ, hy⟩, ?_⟩
  have h2 := mem_pushObj.mp (mem_pushObj_res V N (inf_le_left : Q ⊓ T ≤ Q) hmem)
  rw [res_res, res_res] at h2
  show res M (V.ι.image_mono (pre_mono V (inf_le_right : Q ⊓ T ≤ T)))
      (res M (image_pre_le V T) s) ∈ N.obj (op (pre V (Q ⊓ T)))
  rw [res_res]
  exact h2

/-- The **push** of a submodule of the restriction of `M` to an open `V`: a submodule of `M`
which constrains a section only over `V`. -/
noncomputable def push (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι)) :
    SheafOfModules.Submodule M where
  obj T := pushObj V N T.unop
  map {T T'} f s hs := mem_pushObj_res V N (leOfHom f.unop) hs
  isSheaf := by
    intro T s hs
    rw [Opens.mem_grothendieckTopology] at hs
    refine mem_pushObj_of_local V N s fun x hx => ?_
    obtain ⟨Q, f, hf, hxQ⟩ := hs x hx
    exact ⟨Q, leOfHom f, hxQ, hf⟩

/-- Membership in the push. -/
lemma mem_push_iff (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι)) {T : X.Opens}
    (s : Γ(M, T)) : s ∈ (push V N).obj (op T) ↔
      res M (image_pre_le V T) s ∈ N.obj (op (pre V T)) := Iff.rfl

/-! ### A submodule as a module, and the inclusion of one submodule into another -/

/-- A monomorphism of `𝒪_X`-modules is recognized by injectivity on sections. -/
lemma mono_of_injective_app (a : A ⟶ M) (h : ∀ T : X.Opens, Function.Injective (a.app T)) :
    Mono a := by
  refine (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map ?_
  exact PresheafOfModules.mono_of_injective (f := a.val) fun T => h T.unop

/-- The `𝒪_X`-module underlying a submodule of `M`. This is `toSheafOfModules` at the type
`X.Modules` rather than at `SheafOfModules X.ringCatSheaf`; the two are definitionally equal,
but instances stated for the latter are not found for the former. -/
noncomputable def mod (N : SheafOfModules.Submodule M) : X.Modules := N.toSheafOfModules

/-- The inclusion of a submodule of `M` into `M`. -/
noncomputable def modι (N : SheafOfModules.Submodule M) : mod N ⟶ M := N.ι

/-- A section of the module underlying a submodule, read as a section of `M`. -/
lemma modι_app (N : SheafOfModules.Submodule M) (T : X.Opens) (x : Γ(mod N, T)) :
    (modι N).app T x = (x : ↥(N.obj (op T))).1 := rfl

/-- A section of the module underlying a submodule is a section of that submodule. -/
lemma mem_modι_app (N : SheafOfModules.Submodule M) (T : X.Opens) (x : Γ(mod N, T)) :
    (modι N).app T x ∈ N.obj (op T) := (x : ↥(N.obj (op T))).2

/-- The inclusion of a submodule of `M` into `M` is a monomorphism. -/
instance (N : SheafOfModules.Submodule M) : Mono (modι N) :=
  mono_of_injective_app _ fun _ _ _ hxy => Subtype.val_injective hxy

/-- A section of `M` lying in a submodule, read as a section of the module underlying it. -/
noncomputable def mkSection (N : SheafOfModules.Submodule M) {T : X.Opens} (s : Γ(M, T))
    (hs : s ∈ N.obj (op T)) : Γ(mod N, T) := (⟨s, hs⟩ : ↥(N.obj (op T)))

/-- `mkSection` is a section of `M` again. -/
lemma modι_app_mkSection (N : SheafOfModules.Submodule M) {T : X.Opens} (s : Γ(M, T))
    (hs : s ∈ N.obj (op T)) : (modι N).app T (mkSection N s hs) = s := rfl

/-- The inclusion of one submodule of `M` into another containing it, as a morphism of
`𝒪_X`-modules. -/
noncomputable def inclusion {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T)) : mod N ⟶ mod N' :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (PresheafOfModules.Submodule.homOfLE (N₁ := N.toSubmodule) (N₂ := N'.toSubmodule)
      (fun T => h T.unop))

/-- On sections, the inclusion of submodules does nothing. -/
lemma inclusion_app {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T)) (T : X.Opens) (x : Γ(mod N, T)) :
    (modι N').app T ((inclusion h).app T x) = (modι N).app T x := by
  have hv : (SheafOfModules.forget X.ringCatSheaf).map (inclusion h) =
      PresheafOfModules.Submodule.homOfLE (N₁ := N.toSubmodule) (N₂ := N'.toSubmodule)
        (fun T => h T.unop) :=
    (SheafOfModules.fullyFaithfulForget _).map_preimage _
  show ((SheafOfModules.forget X.ringCatSheaf).map (inclusion h) ≫
    N'.toSubmodule.ι).app (op T) x = _
  rw [hv]
  rfl

/-- The inclusion of submodules is compatible with their inclusions into `M`. -/
lemma inclusion_comp {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T)) :
    inclusion h ≫ modι N' = modι N :=
  Scheme.Modules.hom_ext _ _ fun T => by ext x; exact inclusion_app h T x

/-- An open of an open subscheme has image contained in that open. -/
lemma image_le (W : X.Opens) (T : W.toScheme.Opens) : W.ι ''ᵁ T ≤ W := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- The inclusion of submodules is bijective on sections over an open where they agree. -/
lemma bijective_inclusion_app {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T)) (T : X.Opens)
    (heq : N'.obj (op T) ≤ N.obj (op T)) : Function.Bijective ((inclusion h).app T) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine injective_app (modι N) T ?_
    rw [← inclusion_app h T x, ← inclusion_app h T y, hxy]
  · refine ⟨mkSection N ((modι N').app T y) (heq (mem_modι_app N' T y)), ?_⟩
    refine injective_app (modι N') T ?_
    rw [inclusion_app, modι_app_mkSection]

/-- Restriction along the inclusion of an open reindexes sections. -/
lemma app_restrict_map {A B : X.Modules} (W : X.Opens) (a : A ⟶ B) (T : W.toScheme.Opens) :
    ((Scheme.Modules.restrictFunctor W.ι).map a).app T = a.app (W.ι ''ᵁ T) := rfl

/-- **Two submodules of `M` which agree on the opens contained in `W` have isomorphic
restrictions to `W`**, compatibly with their inclusions into `M` by `inclusion_comp`. -/
lemma isIso_restrict_inclusion (W : X.Opens) {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T))
    (heq : ∀ T : X.Opens, T ≤ W → N'.obj (op T) ≤ N.obj (op T)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (inclusion h)) := by
  refine isIso_of_bijective_app _ fun T => ?_
  rw [app_restrict_map]
  exact bijective_inclusion_app h (W.ι ''ᵁ T) (heq _ (image_le W T))

/-! ### The range of a monomorphism is isomorphic to its source -/

/-- The factorization of a monomorphism through its range, on underlying abelian presheaves. -/
noncomputable def liftAb (a : A ⟶ M) [Mono a] :
    A.presheaf ⟶ (ofMono a).toPresheafOfModules.presheaf where
  app T := AddCommGrpCat.ofHom
    { toFun := fun w => (⟨a.app T.unop w, mem_rangeObj.mpr ⟨w, rfl⟩⟩ : ↥(rangeObj a T.unop))
      map_zero' := Subtype.ext (map_zero (ConcreteCategory.hom (a.app T.unop)))
      map_add' := fun x y => Subtype.ext (map_add (ConcreteCategory.hom (a.app T.unop)) x y) }
  naturality := by
    intro T T' f
    ext w
    exact Subtype.ext (app_res a (leOfHom f.unop) w)

/-- The factorization of a monomorphism through its range. -/
noncomputable def liftOfMono (a : A ⟶ M) [Mono a] : A ⟶ mod (ofMono a) :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (PresheafOfModules.homMk (liftAb a) fun _ r m => Subtype.ext (a.app_smul r m))

/-- On sections, the factorization through the range followed by the inclusion of the range is
the original morphism. -/
lemma liftOfMono_app (a : A ⟶ M) [Mono a] (T : X.Opens) (w : Γ(A, T)) :
    (modι (ofMono a)).app T ((liftOfMono a).app T w) = a.app T w := by
  have hv : (SheafOfModules.forget X.ringCatSheaf).map (liftOfMono a) =
      PresheafOfModules.homMk (liftAb a) (fun _ r m => Subtype.ext (a.app_smul r m)) :=
    (SheafOfModules.fullyFaithfulForget _).map_preimage _
  show ((SheafOfModules.forget X.ringCatSheaf).map (liftOfMono a) ≫
    (ofMono a).toSubmodule.ι).app (op T) w = _
  rw [hv]
  rfl

/-- The factorization through the range followed by the inclusion of the range is the original
morphism. -/
lemma liftOfMono_comp (a : A ⟶ M) [Mono a] : liftOfMono a ≫ modι (ofMono a) = a :=
  Scheme.Modules.hom_ext _ _ fun T => by ext w; exact liftOfMono_app a T w

/-- The factorization of a monomorphism through its range is an isomorphism. -/
instance isIso_liftOfMono (a : A ⟶ M) [Mono a] : IsIso (liftOfMono a) := by
  refine isIso_of_bijective_app _ fun T => ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine injective_app a T ?_
    rw [← liftOfMono_app a T x, ← liftOfMono_app a T y, hxy]
  · obtain ⟨w, hw⟩ := mem_modι_app (ofMono a) T y
    refine ⟨w, ?_⟩
    refine injective_app (modι (ofMono a)) T ?_
    rw [liftOfMono_app]
    exact hw

/-- **The range of a monomorphism is isomorphic to its source**, over the common target. -/
noncomputable def isoOfMono (a : A ⟶ M) [Mono a] : A ≅ mod (ofMono a) := asIso (liftOfMono a)

/-- The isomorphism of a monomorphism with its range is compatible with the inclusions into the
target. -/
lemma isoOfMono_hom_comp (a : A ⟶ M) [Mono a] :
    (isoOfMono a).hom ≫ modι (ofMono a) = a := liftOfMono_comp a

/-! ### The restriction of a push to the open it came from -/

/-- Membership in a submodule is unchanged by restriction along an equality of opens. -/
lemma mem_iff_of_eq (N : SheafOfModules.Submodule M) {T T' : X.Opens} (he : T' = T)
    (h : T' ≤ T) (s : Γ(M, T)) : res M h s ∈ N.obj (op T') ↔ s ∈ N.obj (op T) := by
  subst he
  rw [res_self]

/-- The preimage of the image of an open of an open subscheme is that open. -/
lemma pre_image_eq (V : X.Opens) (W : V.toScheme.Opens) : pre V (V.ι ''ᵁ W) = W := by
  simp [pre]

/-- Over an open of the form `V.ι ''ᵁ W`, the push of `N` has exactly the sections of `N`. -/
lemma mem_push_iff_image (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι))
    (W : V.toScheme.Opens) (s : Γ(M, V.ι ''ᵁ W)) :
    s ∈ (push V N).obj (op (V.ι ''ᵁ W)) ↔ s ∈ N.obj (op W) := by
  rw [mem_push_iff]
  exact mem_iff_of_eq (M := M.restrict V.ι) N (pre_image_eq V W)
    (le_of_eq (pre_image_eq V W)) s

/-- The comparison of `N` with the restriction to `V` of its push, on underlying abelian
presheaves. -/
noncomputable def pushAb (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι)) :
    (mod N).presheaf ⟶ ((mod (push V N)).restrict V.ι).val.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun x =>
        (⟨(x : ↥(N.obj W)).1, (mem_push_iff_image V N W.unop _).mpr (x : ↥(N.obj W)).2⟩ :
          ↥((push V N).obj (op (V.ι ''ᵁ W.unop))))
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  naturality := by
    intro W W' f
    ext x
    exact Subtype.ext rfl

/-- The comparison of `N` with the restriction to `V` of its push. -/
noncomputable def pushRestrictHom (V : X.Opens)
    (N : SheafOfModules.Submodule (M.restrict V.ι)) :
    mod N ⟶ (mod (push V N)).restrict V.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (PresheafOfModules.homMk (pushAb V N) fun _ _ _ => Subtype.ext rfl)

/-- The comparison map does nothing on sections. -/
lemma pushRestrictHom_app_val (V : X.Opens) (N : SheafOfModules.Submodule (M.restrict V.ι))
    (W : V.toScheme.Opens) (x : Γ(mod N, W)) :
    ((pushRestrictHom V N).app W x : ↥((push V N).obj (op (V.ι ''ᵁ W)))).1 =
      (x : ↥(N.obj (op W))).1 := by
  have hv : (SheafOfModules.forget V.toScheme.ringCatSheaf).map (pushRestrictHom V N) =
      PresheafOfModules.homMk (pushAb V N) (fun _ _ _ => Subtype.ext rfl) :=
    (SheafOfModules.fullyFaithfulForget _).map_preimage _
  show (((SheafOfModules.forget V.toScheme.ringCatSheaf).map
    (pushRestrictHom V N)).app (op W) x : ↥((push V N).obj (op (V.ι ''ᵁ W)))).1 = _
  rw [hv]
  rfl

/-- The comparison of `N` with the restriction to `V` of its push is an isomorphism. -/
instance isIso_pushRestrictHom (V : X.Opens)
    (N : SheafOfModules.Submodule (M.restrict V.ι)) : IsIso (pushRestrictHom V N) := by
  refine isIso_of_bijective_app _ fun W => ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h := congrArg (fun z => (z : ↥((push V N).obj (op (V.ι ''ᵁ W)))).1) hxy
    simp only [pushRestrictHom_app_val] at h
    exact Subtype.ext h
  · refine ⟨(⟨(y : ↥((push V N).obj (op (V.ι ''ᵁ W)))).1,
      (mem_push_iff_image V N W _).mp (y : ↥((push V N).obj (op (V.ι ''ᵁ W)))).2⟩ :
        ↥(N.obj (op W))), ?_⟩
    exact Subtype.ext (pushRestrictHom_app_val V N W _)

/-- **The restriction to `V` of the push of `N` is `N`.** -/
noncomputable def pushRestrictIso (V : X.Opens)
    (N : SheafOfModules.Submodule (M.restrict V.ι)) :
    mod N ≅ (mod (push V N)).restrict V.ι := asIso (pushRestrictHom V N)

/-- The identification of `N` with the restriction of its push respects the inclusions into the
restriction of `M`. -/
lemma pushRestrictIso_hom_comp (V : X.Opens)
    (N : SheafOfModules.Submodule (M.restrict V.ι)) :
    (pushRestrictIso V N).hom ≫
      (Scheme.Modules.restrictFunctor V.ι).map (modι (push V N)) = modι N := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  rw [Scheme.Modules.Hom.comp_app]
  show (modι (push V N)).app (V.ι ''ᵁ W) ((pushRestrictHom V N).app W x) = _
  simp only [modι_app]
  exact pushRestrictHom_app_val V N W x

/-! ### The hypotheses of the gluing, for a push -/

/-- **The push imposes no condition away from `V`.** If `B` is contained in `N` over the opens of
the form `V.ι ''ᵁ W'` that lie in `W`, then `B` is contained in the push of `N` over every open
contained in `W` — including the opens disjoint from `V`, over which the push is everything. -/
theorem le_push_of_le_image (B : SheafOfModules.Submodule M) {V W : X.Opens}
    (N : SheafOfModules.Submodule (M.restrict V.ι))
    (hagree : ∀ (W' : V.toScheme.Opens), V.ι ''ᵁ W' ≤ W → ∀ s : Γ(M, V.ι ''ᵁ W'),
      s ∈ B.obj (op (V.ι ''ᵁ W')) → s ∈ N.obj (op W'))
    (T : X.Opens) (hT : T ≤ W) : B.obj (op T) ≤ (push V N).obj (op T) := by
  intro s hs
  refine (mem_push_iff V N s).mpr ?_
  exact hagree (pre V T) ((image_pre_le V T).trans hT) _ (mem_of_le B _ hs)

/-- **Over `V` the push is contained in `B` as soon as `N` is.** -/
theorem push_le_of_le_image (B : SheafOfModules.Submodule M) {V : X.Opens}
    (N : SheafOfModules.Submodule (M.restrict V.ι))
    (hNB : ∀ (W' : V.toScheme.Opens) (s : Γ(M, V.ι ''ᵁ W')),
      s ∈ N.obj (op W') → s ∈ B.obj (op (V.ι ''ᵁ W')))
    (T : X.Opens) (hT : T ≤ V) : (push V N).obj (op T) ≤ B.obj (op T) := by
  intro s hs
  have h1 : res M (image_pre_le V T) s ∈ B.obj (op (V.ι ''ᵁ pre V T)) :=
    hNB (pre V T) _ ((mem_push_iff V N s).mp hs)
  exact (mem_iff_of_eq B (image_pre_eq V hT) (image_pre_le V T) s).mp h1

end Stacks.AlgebraicGeometry.Subsheaf
