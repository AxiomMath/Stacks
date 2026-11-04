module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerDegreeFiltration
import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple

/-!
# Ideal-power cohomology and the ideal powers of cohomology are pro-isomorphic

Let `X` be a Noetherian scheme, `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `𝓕^•` a complex of
coherent `𝒪_X`-modules, with no boundedness assumed. Fix `p` and write `𝓗 = H^p(𝓕^•)` and
`𝓗_n = H^p(𝓘^n𝓕^•)`. For one constant `c > 0` and every `n ≥ c` the canonical map `𝓗_n → 𝓗`
factors through `𝓘^(n-c)𝓗`, there is a canonical map `𝓘^n𝓗 → 𝓗_(n-c)` back, and the two
composites `𝓗_n → 𝓘^(n-c)𝓗 → 𝓗_(n-2c)` and `𝓘^n𝓗 → 𝓗_(n-c) → 𝓘^(n-2c)𝓗` are the canonical
maps. Hence the two inverse systems are isomorphic as pro-objects, by the cofinal shift
`n ↦ n + c`.

Everything is computed inside the single module `𝓕^p`. Both cohomologies in degree `p` are
subquotients of `𝓕^p`: the homology of a short complex is the sectionwise image of the first map
inside the sectionwise kernel of the second, and a degreewise monomorphism of complexes carries
that presentation into the ambient complex. So `𝓗` is `Z/B` and `𝓗_n` is
`(Z ⊓ 𝓘^n𝓕^p)/d(𝓘^n𝓕^(p-1))`, while `𝓘^m𝓗` is `(𝓘^mZ)/(𝓘^mZ ⊓ B)`. In this model every map in
sight is the map of subquotients induced by an inclusion of pairs of submodules, conjugated by
those identifications, so each of the identities above is an instance of the composition law for
such maps, and the only input with mathematical content is the pair of Artin-Rees containments
`Z ⊓ 𝓘^n𝓕^p ⊆ 𝓘^(n-c)Z` and `B ⊓ 𝓘^n𝓕^p ⊆ d(𝓘^(n-c)𝓕^(p-1))`.

## Main definitions

* `Stacks.Duality.pushSubqIso` — the homology of a short complex as a subquotient of an ambient
  module, along a monomorphism out of its middle term.
* `Stacks.Duality.homologySubqIso`, `Stacks.Duality.cohIso` and
  `Stacks.Duality.idealPowerSubqIso` — the presentations of `𝓗`, `𝓗_n` and `𝓘^m𝓗` as
  subquotients of `𝓕^p`.
* `Stacks.Duality.tauMap`, `Stacks.Duality.rhoMap`, `Stacks.Duality.psiMap` — the canonical maps
  `𝓗_m → 𝓗_n`, `𝓗_n → 𝓘^a𝓗` and `𝓘^n𝓗 → 𝓗_b`.

## Main results

* `Stacks.Duality.homologyMap_comp_pushSubqIso_hom` — a morphism of short complexes compatible
  with two monomorphisms into one module induces the map of subquotients of that module.
* `Stacks.Duality.rhoMap_comp_subι` and `Stacks.Duality.psiMap_comp_cohomologyToOriginal` — the
  image containment and the canonicity of the map back.
* `Stacks.Duality.rhoMap_comp_psiMap` and `Stacks.Duality.psiMap_comp_rhoMap` — the two
  composites.
* `Stacks.Duality.cohomologyIdealPowers_proIsomorphic` — Tag 0G4R: the pro-isomorphism.

## References

* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
* [Stacks Project, Tag 0G3K](https://stacks.math.columbia.edu/tag/0G3K)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Stacks.Duality

variable {X : Scheme.{u}}

attribute [local instance] AlgebraicGeometry.sectionsModuleΓSheaf

/-! ### Transport and composition of maps of subquotients -/

/-- An identity conjugated by an isomorphism is the identity. -/
lemma hom_conj_id {C : Type w} [Category.{v} C] {A A' : C} (a : A ≅ A') :
    a.hom ≫ 𝟙 A' ≫ a.inv = 𝟙 A :=
  (congrArg (fun t => a.hom ≫ t) (Category.id_comp a.inv)).trans a.hom_inv_id

/-- Conjugation by isomorphisms is compatible with composition. -/
lemma hom_conj_comp {C : Type w} [Category.{v} C] {A A' B B' D D' : C}
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (r : A' ⟶ B') (s : B' ⟶ D') :
    (a.hom ≫ r ≫ b.inv) ≫ (b.hom ≫ s ≫ d.inv) = a.hom ≫ (r ≫ s) ≫ d.inv := by
  simp

/-- A morphism that intertwines two isomorphisms is their conjugate. -/
lemma hom_conj_eq {C : Type w} [Category.{v} C] {A A' B B' : C} (a : A ≅ A') (b : B ≅ B')
    (r : A' ⟶ B') (f : A ⟶ B) (h : f ≫ b.hom = a.hom ≫ r) : f = a.hom ≫ r ≫ b.inv :=
  ((Category.comp_id f).symm.trans (congrArg (fun t => f ≫ t) b.hom_inv_id.symm)).trans
    ((Category.assoc f b.hom b.inv).symm.trans
      ((congrArg (fun t => t ≫ b.inv) h).trans (Category.assoc a.hom r b.inv)))

/-- Pasting two commuting squares. -/
lemma paste_comp_comp {C : Type w} [Category.{v} C] {W Y Z Y' Z' T : C}
    (a : W ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) (d : W ⟶ Y') (g : Y' ⟶ Z) (e : Y' ⟶ Z')
    (f : Z' ⟶ T) (h1 : a ≫ b = d ≫ g) (h2 : g ≫ c = e ≫ f) :
    a ≫ (b ≫ c) = (d ≫ e) ≫ f :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ c) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => d ≫ t) h2).trans (Category.assoc _ _ _).symm)))

/-- Equal numerators and denominators give the same subquotient of `L`; the isomorphism is the
induced map of subquotients. -/
def subqEqIso {L : X.Modules} {N M N' M' : L.Submodule} (h : N ≤ M) (h' : N' ≤ M')
    (hN : N = N') (hM : M = M') : subq N M h ≅ subq N' M' h' where
  hom := subqMap h h' hM.le hN.le
  inv := subqMap h' h hM.ge hN.ge
  hom_inv_id := (subqMap_comp h h' h hM.le hN.le hM.ge hN.ge).trans (subqMap_id h)
  inv_hom_id := (subqMap_comp h' h h' hM.ge hN.ge hM.le hN.le).trans (subqMap_id h')

/-- A composite of maps of subquotients, read through lifts to the numerators. The three
subquotients may sit in three different ambient modules. -/
lemma subqπ_comp_comp {L L' L'' : X.Modules} {N M : L.Submodule} {N' M' : L'.Submodule}
    {N'' M'' : L''.Submodule} (h : N ≤ M) (h' : N' ≤ M') (h'' : N'' ≤ M'')
    (a : subq N M h ⟶ subq N' M' h') (b : subq N' M' h' ⟶ subq N'' M'' h'')
    (u : (M.toSheafOfModules : X.Modules) ⟶ (M'.toSheafOfModules : X.Modules))
    (v : (M'.toSheafOfModules : X.Modules) ⟶ (M''.toSheafOfModules : X.Modules))
    (ha : subqπ N M h ≫ a = u ≫ subqπ N' M' h')
    (hb : subqπ N' M' h' ≫ b = v ≫ subqπ N'' M'' h'') :
    subqπ N M h ≫ (a ≫ b) = (u ≫ v) ≫ subqπ N'' M'' h'' :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ b) ha).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => u ≫ t) hb).trans (Category.assoc _ _ _).symm)))

/-- Two maps of subquotients agree as soon as lifts of them to the numerators agree in the
ambient module. -/
lemma subq_hom_ext {L L' : X.Modules} {N M : L.Submodule} {N' M' : L'.Submodule} (h : N ≤ M)
    (h' : N' ≤ M') {a b : subq N M h ⟶ subq N' M' h'}
    {u v : (M.toSheafOfModules : X.Modules) ⟶ (M'.toSheafOfModules : X.Modules)}
    (ha : subqπ N M h ≫ a = u ≫ subqπ N' M' h')
    (hb : subqπ N M h ≫ b = v ≫ subqπ N' M' h')
    (huv : u ≫ subι M' = v ≫ subι M') : a = b :=
  (cancel_epi (subqπ N M h)).1
    (ha.trans ((congrArg (fun t => t ≫ subqπ N' M' h') (cancel_subι M' u v huv)).trans hb.symm))

/-! ### Homology as a subquotient of an ambient module -/

/-- A morphism carries a submodule of its source into the image of that submodule. -/
lemma le_comap_imageSubmodule_subι_comp {M L : X.Modules} (j : M ⟶ L) (K : M.Submodule) :
    K ≤ sheafSubmoduleComap j (imageSubmodule (subι K ≫ j)) :=
  (le_of_eq (imageSubmodule_subι K).symm).trans
    (imageSubmodule_le_comap (subι K) (subι K ≫ j) (𝟙 _) j (Category.id_comp _).symm)

/-- The comparison of a subquotient of `M` with the corresponding subquotient of `L`, read through
the lift to the numerators. -/
lemma subqπ_comp_subqPushIso_hom {M L : X.Modules} (j : M ⟶ L) (hj : Mono j)
    (N M' : M.Submodule) (h : N ≤ M') :
    subqπ N M' h ≫ (subqPushIso j hj N M' h).hom =
      sheafSubmoduleMap j M' (imageSubmodule (subι M' ≫ j))
          (le_comap_imageSubmodule_subι_comp j M') ≫
        subqπ (imageSubmodule (subι N ≫ j)) (imageSubmodule (subι M' ≫ j))
          (imageSubmodule_subι_comp_mono j h) :=
  (congrArg (fun t => subqπ N M' h ≫ t)
      (subqPushIso_hom_eq j hj N M' h (le_comap_imageSubmodule_subι_comp j M')
        (le_comap_imageSubmodule_subι_comp j N))).trans
    (subqπ_comp_subqMapAlong j h (imageSubmodule_subι_comp_mono j h)
      (le_comap_imageSubmodule_subι_comp j M') (le_comap_imageSubmodule_subι_comp j N))

/-- **The homology of a short complex as a subquotient of an ambient module.** A monomorphism
`j : S.X₂ ⟶ L` presents the homology of `S` as the image of the cycles modulo the image of the
boundaries, inside `L`. -/
def pushSubqIso (T : ShortComplex X.Modules) {L : X.Modules} (j : T.X₂ ⟶ L) (hj : Mono j) :
    T.homology ≅ subq (imageSubmodule (subι (imageSubmodule T.f) ≫ j))
      (imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule T.g) ≫ j))
      (imageSubmodule_subι_comp_mono j (imageSubmodule_le_kernelSubmodule T.f T.g T.zero)) :=
  homologyIsoSubq T ≪≫ subqPushIso j hj (imageSubmodule T.f)
    (Stacks.Algebraization.kernelSubmodule T.g)
    (imageSubmodule_le_kernelSubmodule T.f T.g T.zero)

/-- The forward map of `pushSubqIso` is the composite of `homologyIsoSubq` with the forward map
of `subqPushIso`. -/
lemma pushSubqIso_hom (T : ShortComplex X.Modules) {L : X.Modules} (j : T.X₂ ⟶ L)
    (hj : Mono j) :
    (pushSubqIso T j hj).hom = (homologyIsoSubq T).hom ≫
      (subqPushIso j hj (imageSubmodule T.f) (Stacks.Algebraization.kernelSubmodule T.g)
        (imageSubmodule_le_kernelSubmodule T.f T.g T.zero)).hom := rfl

/-- **The push isomorphism is natural.** A morphism `t : M₁ ⟶ M₂` compatible with two
monomorphisms into one ambient module carries the comparison of subquotients over `M₁` to the one
over `M₂`. -/
lemma subqMapAlong_comp_subqPushIso_hom {M₁ M₂ L : X.Modules} (t : M₁ ⟶ M₂)
    (j₁ : M₁ ⟶ L) (hj₁ : Mono j₁) (j₂ : M₂ ⟶ L) (hj₂ : Mono j₂) (hj : t ≫ j₂ = j₁)
    {N₁ P₁ : M₁.Submodule} {N₂ P₂ : M₂.Submodule} (h₁ : N₁ ≤ P₁) (h₂ : N₂ ≤ P₂)
    (hk : P₁ ≤ sheafSubmoduleComap t P₂) (hi : N₁ ≤ sheafSubmoduleComap t N₂)
    (hN : imageSubmodule (subι N₁ ≫ j₁) ≤ imageSubmodule (subι N₂ ≫ j₂))
    (hM : imageSubmodule (subι P₁ ≫ j₁) ≤ imageSubmodule (subι P₂ ≫ j₂)) :
    subqMapAlong t h₁ h₂ hk hi ≫ (subqPushIso j₂ hj₂ N₂ P₂ h₂).hom =
      (subqPushIso j₁ hj₁ N₁ P₁ h₁).hom ≫
        subqMap (imageSubmodule_subι_comp_mono j₁ h₁)
          (imageSubmodule_subι_comp_mono j₂ h₂) hM hN := by
  have hA := subqπ_comp_comp h₁ h₂ (imageSubmodule_subι_comp_mono j₂ h₂)
    (subqMapAlong t h₁ h₂ hk hi) (subqPushIso j₂ hj₂ N₂ P₂ h₂).hom
    (sheafSubmoduleMap t P₁ P₂ hk)
    (sheafSubmoduleMap j₂ P₂ (imageSubmodule (subι P₂ ≫ j₂))
      (le_comap_imageSubmodule_subι_comp j₂ P₂))
    (subqπ_comp_subqMapAlong t h₁ h₂ hk hi)
    (subqπ_comp_subqPushIso_hom j₂ hj₂ N₂ P₂ h₂)
  have hB := subqπ_comp_comp h₁ (imageSubmodule_subι_comp_mono j₁ h₁)
    (imageSubmodule_subι_comp_mono j₂ h₂) (subqPushIso j₁ hj₁ N₁ P₁ h₁).hom
    (subqMap (imageSubmodule_subι_comp_mono j₁ h₁)
      (imageSubmodule_subι_comp_mono j₂ h₂) hM hN)
    (sheafSubmoduleMap j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
      (le_comap_imageSubmodule_subι_comp j₁ P₁)) (subHom hM)
    (subqπ_comp_subqPushIso_hom j₁ hj₁ N₁ P₁ h₁)
    (subqπ_comp_subqMap (imageSubmodule_subι_comp_mono j₁ h₁)
      (imageSubmodule_subι_comp_mono j₂ h₂) hM hN)
  refine subq_hom_ext h₁ (imageSubmodule_subι_comp_mono j₂ h₂) hA hB ?_
  calc (sheafSubmoduleMap t P₁ P₂ hk ≫
          sheafSubmoduleMap j₂ P₂ (imageSubmodule (subι P₂ ≫ j₂))
            (le_comap_imageSubmodule_subι_comp j₂ P₂)) ≫
        subι (imageSubmodule (subι P₂ ≫ j₂))
      = sheafSubmoduleMap t P₁ P₂ hk ≫
          (sheafSubmoduleMap j₂ P₂ (imageSubmodule (subι P₂ ≫ j₂))
              (le_comap_imageSubmodule_subι_comp j₂ P₂) ≫
            subι (imageSubmodule (subι P₂ ≫ j₂))) := Category.assoc _ _ _
    _ = sheafSubmoduleMap t P₁ P₂ hk ≫ (subι P₂ ≫ j₂) :=
        congrArg (fun w => sheafSubmoduleMap t P₁ P₂ hk ≫ w)
          (sheafSubmoduleMap_comp_subι j₂ P₂ (imageSubmodule (subι P₂ ≫ j₂))
            (le_comap_imageSubmodule_subι_comp j₂ P₂))
    _ = (sheafSubmoduleMap t P₁ P₂ hk ≫ subι P₂) ≫ j₂ := (Category.assoc _ _ _).symm
    _ = (subι P₁ ≫ t) ≫ j₂ :=
        congrArg (fun w => w ≫ j₂) (sheafSubmoduleMap_comp_subι t P₁ P₂ hk)
    _ = subι P₁ ≫ (t ≫ j₂) := Category.assoc _ _ _
    _ = subι P₁ ≫ j₁ := congrArg (fun w => subι P₁ ≫ w) hj
    _ = sheafSubmoduleMap j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
          (le_comap_imageSubmodule_subι_comp j₁ P₁) ≫
          subι (imageSubmodule (subι P₁ ≫ j₁)) :=
        (sheafSubmoduleMap_comp_subι j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
          (le_comap_imageSubmodule_subι_comp j₁ P₁)).symm
    _ = sheafSubmoduleMap j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
          (le_comap_imageSubmodule_subι_comp j₁ P₁) ≫
          (subHom hM ≫ subι (imageSubmodule (subι P₂ ≫ j₂))) :=
        congrArg (fun w => sheafSubmoduleMap j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
          (le_comap_imageSubmodule_subι_comp j₁ P₁) ≫ w) (homOfLE_comp_subι hM).symm
    _ = (sheafSubmoduleMap j₁ P₁ (imageSubmodule (subι P₁ ≫ j₁))
          (le_comap_imageSubmodule_subι_comp j₁ P₁) ≫ subHom hM) ≫
          subι (imageSubmodule (subι P₂ ≫ j₂)) := (Category.assoc _ _ _).symm

/-- **Functoriality of the subquotient model of homology.** A morphism of short complexes which is
compatible with two monomorphisms into a single ambient module induces the map of subquotients of
that module. -/
lemma homologyMap_comp_pushSubqIso_hom (S₁ S₂ : ShortComplex X.Modules) (φ : S₁ ⟶ S₂)
    {L : X.Modules} (j₁ : S₁.X₂ ⟶ L) (hj₁ : Mono j₁) (j₂ : S₂.X₂ ⟶ L) (hj₂ : Mono j₂)
    (hj : φ.τ₂ ≫ j₂ = j₁)
    (hN : imageSubmodule (subι (imageSubmodule S₁.f) ≫ j₁) ≤
      imageSubmodule (subι (imageSubmodule S₂.f) ≫ j₂))
    (hM : imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule S₁.g) ≫ j₁) ≤
      imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule S₂.g) ≫ j₂)) :
    ShortComplex.homologyMap φ ≫ (pushSubqIso S₂ j₂ hj₂).hom =
      (pushSubqIso S₁ j₁ hj₁).hom ≫
        subqMap (imageSubmodule_subι_comp_mono j₁
            (imageSubmodule_le_kernelSubmodule S₁.f S₁.g S₁.zero))
          (imageSubmodule_subι_comp_mono j₂
            (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero)) hM hN := by
  have hk : Stacks.Algebraization.kernelSubmodule S₁.g ≤
      sheafSubmoduleComap φ.τ₂ (Stacks.Algebraization.kernelSubmodule S₂.g) :=
    kernelSubmodule_le_comap S₁.g S₂.g φ.τ₂ φ.τ₃ φ.comm₂₃
  have hi : imageSubmodule S₁.f ≤ sheafSubmoduleComap φ.τ₂ (imageSubmodule S₂.f) :=
    imageSubmodule_le_comap S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  have key := subqMapAlong_comp_subqPushIso_hom φ.τ₂ j₁ hj₁ j₂ hj₂ hj
    (imageSubmodule_le_kernelSubmodule S₁.f S₁.g S₁.zero)
    (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero) hk hi hN hM
  calc ShortComplex.homologyMap φ ≫ (pushSubqIso S₂ j₂ hj₂).hom
      = ShortComplex.homologyMap φ ≫ ((homologyIsoSubq S₂).hom ≫
          (subqPushIso j₂ hj₂ (imageSubmodule S₂.f)
            (Stacks.Algebraization.kernelSubmodule S₂.g) _).hom) :=
        congrArg (fun t => ShortComplex.homologyMap φ ≫ t) (pushSubqIso_hom S₂ j₂ hj₂)
    _ = (ShortComplex.homologyMap φ ≫ (homologyIsoSubq S₂).hom) ≫
          (subqPushIso j₂ hj₂ (imageSubmodule S₂.f)
            (Stacks.Algebraization.kernelSubmodule S₂.g) _).hom :=
        (Category.assoc _ _ _).symm
    _ = ((homologyIsoSubq S₁).hom ≫ subqMapAlong φ.τ₂ _ _ hk hi) ≫
          (subqPushIso j₂ hj₂ (imageSubmodule S₂.f)
            (Stacks.Algebraization.kernelSubmodule S₂.g) _).hom :=
        congrArg (fun t => t ≫ (subqPushIso j₂ hj₂ (imageSubmodule S₂.f)
          (Stacks.Algebraization.kernelSubmodule S₂.g) _).hom)
          (homologyMap_comp_homologyIsoSubq_hom φ hk hi)
    _ = (homologyIsoSubq S₁).hom ≫ (subqMapAlong φ.τ₂ _ _ hk hi ≫
          (subqPushIso j₂ hj₂ (imageSubmodule S₂.f)
            (Stacks.Algebraization.kernelSubmodule S₂.g) _).hom) :=
        Category.assoc _ _ _
    _ = (homologyIsoSubq S₁).hom ≫ ((subqPushIso j₁ hj₁ (imageSubmodule S₁.f)
          (Stacks.Algebraization.kernelSubmodule S₁.g) _).hom ≫ subqMap _ _ hM hN) :=
        congrArg (fun t => (homologyIsoSubq S₁).hom ≫ t) key
    _ = ((homologyIsoSubq S₁).hom ≫ (subqPushIso j₁ hj₁ (imageSubmodule S₁.f)
          (Stacks.Algebraization.kernelSubmodule S₁.g) _).hom) ≫ subqMap _ _ hM hN :=
        (Category.assoc _ _ _).symm
    _ = (pushSubqIso S₁ j₁ hj₁).hom ≫ subqMap _ _ hM hN :=
        congrArg (fun t => t ≫ subqMap _ _ hM hN) (pushSubqIso_hom S₁ j₁ hj₁).symm

/-! ### The terms of an ideal-power subcomplex sit inside the terms of the complex -/

variable (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (p : ℤ)

/-- The inclusion of `𝓘^n𝓕^•` into `𝓕^•` is injective on sections in every degree. -/
lemma injective_secMap_inclusion_f (S : IdealPowerComplexSystem I F) (n : ℕ) (i : ℤ)
    (U : X.Opens) : Function.Injective (secMap ((S.inclusion n).f i) U) := by
  rw [← S.include_f n i]
  exact injective_app_comp (U := op U) ((S.termIso n i).hom)
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n (F.X i)).ι
    (injective_secMap_of_isIso _ (isIso_hom_of_iso _) U)
    (injective_subι_app (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n (F.X i))
      (op U))

/-- The inclusion of `𝓘^n𝓕^•` into `𝓕^•` is a monomorphism in every degree. -/
lemma mono_inclusion_f (S : IdealPowerComplexSystem I F) (n : ℕ) (i : ℤ) :
    Mono ((S.inclusion n).f i) :=
  mono_of_injective_app_affine _ fun U => injective_secMap_inclusion_f I F S n i U.1

/-- The image of `𝓘^n𝓕^p` in `𝓕^p` is the submodule `𝓘^n𝓕^p`. -/
lemma imageSubmodule_inclusion_f (S : IdealPowerComplexSystem I F) (n : ℕ) :
    imageSubmodule ((S.inclusion n).f p) = pwSub I F p n := by
  have hepi : Epi (S.termIso n p).hom := epi_of_isIso_modules _ (isIso_hom_of_iso _)
  rw [← S.include_f n p]
  refine (@imageSubmodule_epi_comp X _ _ _ _ hepi _).trans ?_
  exact (imageSubmodule_subι
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n (F.X p))).trans
    (idealPowerMultiple_eq_algebraization I n ((F.sc p).X₂))

/-- The image in `𝓕^p` of the boundaries of `𝓘^n𝓕^•` is `d(𝓘^n𝓕^{p-1})`. -/
lemma imageSubmodule_bdry_inclusion (S : IdealPowerComplexSystem I F) (n : ℕ) :
    imageSubmodule (subι (imageSubmodule ((S.complex n).sc p).f) ≫ (S.inclusion n).f p) =
      bdryPwSub I F p n :=
  have hepi : Epi (S.termIso n ((ComplexShape.up ℤ).prev p)).hom :=
    epi_of_isIso_modules _ (isIso_hom_of_iso _)
  have hA : (S.inclusion n).f ((ComplexShape.up ℤ).prev p) ≫ (F.sc p).f =
      (S.termIso n ((ComplexShape.up ℤ).prev p)).hom ≫
        (subι (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n ((F.sc p).X₁)) ≫
          (F.sc p).f) :=
    calc (S.inclusion n).f ((ComplexShape.up ℤ).prev p) ≫ (F.sc p).f
        = ((S.termIso n ((ComplexShape.up ℤ).prev p)).hom ≫
            subι (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n
              ((F.sc p).X₁))) ≫ (F.sc p).f :=
          congrArg (fun t => t ≫ (F.sc p).f)
            (S.include_f n ((ComplexShape.up ℤ).prev p)).symm
      _ = (S.termIso n ((ComplexShape.up ℤ).prev p)).hom ≫
            (subι (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n
              ((F.sc p).X₁)) ≫ (F.sc p).f) :=
          Category.assoc _ _ _
  (imageSubmodule_subι_comp_imageSubmodule ((S.complex n).sc p).f ((S.inclusion n).f p)).trans
    ((congrArg (fun t : (S.complex n).X ((ComplexShape.up ℤ).prev p) ⟶ (F.sc p).X₂ =>
          imageSubmodule t)
        (((S.inclusion n).comm ((ComplexShape.up ℤ).prev p) p).symm.trans hA)).trans
      ((@imageSubmodule_epi_comp X _ _ _ _ hepi _).trans
        (congrArg (fun K : ((F.sc p).X₁).Submodule => imageSubmodule (subι K ≫ (F.sc p).f))
          (idealPowerMultiple_eq_algebraization I n ((F.sc p).X₁)))))

/-- The image in `𝓕^p` of the cycles of `𝓘^n𝓕^•` is `Z ⊓ 𝓘^n𝓕^p`. -/
lemma imageSubmodule_cyc_inclusion (S : IdealPowerComplexSystem I F) (n : ℕ) :
    imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule ((S.complex n).sc p).g) ≫
      (S.inclusion n).f p) = cycSub F p ⊓ pwSub I F p n := by
  refine (imageSubmodule_subι_kernelSubmodule_comp ((S.inclusion n).f p)
    (mono_inclusion_f I F S n p) ((S.complex n).sc p).g (F.sc p).g
    ((S.inclusion n).f ((ComplexShape.up ℤ).next p))
    (injective_secMap_inclusion_f I F S n ((ComplexShape.up ℤ).next p))
    ((S.inclusion n).comm p ((ComplexShape.up ℤ).next p))).trans ?_
  rw [imageSubmodule_inclusion_f I F p S n]
  exact inf_comm _ _

/-- The boundaries of `𝓘^n𝓕^•`, seen in `𝓕^p`, lie in the cycles met with `𝓘^n𝓕^p`. -/
lemma bdryPwSub_le_cycSub_inf_pwSub (hF : TermsCoherent F) (n : ℕ) :
    bdryPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p n :=
  le_inf ((bdryPwSub_le_bdrySub I F p n).trans (bdrySub_le_cycSub F p))
    (bdryPwSub_le_pwSub I F p hF n)

/-! ### The two cohomologies in degree `p` as subquotients of `𝓕^p` -/

/-- The identity of a module on a scheme is a monomorphism. -/
lemma mono_id_modules (M : X.Modules) : Mono (𝟙 M) := inferInstance

/-- Along any morphism out of `𝓕^p`, the image of the boundaries lies in the image of the
cycles. -/
lemma pushBdry_le_pushCyc (T : ShortComplex X.Modules) {L : X.Modules} (j : T.X₂ ⟶ L) :
    imageSubmodule (subι (imageSubmodule T.f) ≫ j) ≤
      imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule T.g) ≫ j) :=
  imageSubmodule_subι_comp_mono j (imageSubmodule_le_kernelSubmodule T.f T.g T.zero)

/-- The homology map of a morphism of short complexes, then a map of subquotients of `L` out of the
target's model, is the source's model followed by the composite map of subquotients. -/
private lemma homologyMap_comp_pushSubqIso_hom_comp_subqMap (S₁ S₂ : ShortComplex X.Modules)
    (φ : S₁ ⟶ S₂) {L : X.Modules} (j₁ : S₁.X₂ ⟶ L) (hj₁ : Mono j₁) (j₂ : S₂.X₂ ⟶ L)
    (hj₂ : Mono j₂) (hj : φ.τ₂ ≫ j₂ = j₁)
    (hN : imageSubmodule (subι (imageSubmodule S₁.f) ≫ j₁) ≤
      imageSubmodule (subι (imageSubmodule S₂.f) ≫ j₂))
    (hM : imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule S₁.g) ≫ j₁) ≤
      imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule S₂.g) ≫ j₂))
    {N M : L.Submodule} (h : N ≤ M)
    (hM₂ : imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule S₂.g) ≫ j₂) ≤ M)
    (hN₂ : imageSubmodule (subι (imageSubmodule S₂.f) ≫ j₂) ≤ N) :
    ShortComplex.homologyMap φ ≫ (pushSubqIso S₂ j₂ hj₂).hom ≫
        subqMap (pushBdry_le_pushCyc S₂ j₂) h hM₂ hN₂ =
      (pushSubqIso S₁ j₁ hj₁).hom ≫
        subqMap (pushBdry_le_pushCyc S₁ j₁) h (hM.trans hM₂) (hN.trans hN₂) := by
  rw [← subqMap_comp (pushBdry_le_pushCyc S₁ j₁) (pushBdry_le_pushCyc S₂ j₂) h hM hN hM₂ hN₂,
    ← Category.assoc, ← Category.assoc,
    homologyMap_comp_pushSubqIso_hom S₁ S₂ φ j₁ hj₁ j₂ hj₂ hj hN hM]

/-- The image of the boundaries of `𝓕^•` under the identity of `𝓕^p` is `B`. -/
lemma imageSubmodule_bdry_id :
    imageSubmodule (subι (imageSubmodule (F.sc p).f) ≫ 𝟙 ((F.sc p).X₂)) = bdrySub F p :=
  (imageSubmodule_subι_comp_imageSubmodule (F.sc p).f (𝟙 ((F.sc p).X₂))).trans
    (congrArg imageSubmodule (Category.comp_id (F.sc p).f))

/-- The image of the cycles of `𝓕^•` under the identity of `𝓕^p` is `Z`. -/
lemma imageSubmodule_cyc_id :
    imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule (F.sc p).g) ≫
      𝟙 ((F.sc p).X₂)) = cycSub F p :=
  (congrArg imageSubmodule
      (Category.comp_id (subι (Stacks.Algebraization.kernelSubmodule (F.sc p).g)))).trans
    (imageSubmodule_subι (Stacks.Algebraization.kernelSubmodule (F.sc p).g))

/-- **`H^p(𝓕^•)` is the subquotient `Z / B` of `𝓕^p`.** -/
def homologySubqIso : F.homology p ≅ homSub F p :=
  pushSubqIso (F.sc p) (𝟙 ((F.sc p).X₂)) (mono_id_modules ((F.sc p).X₂)) ≪≫
    subqEqIso (pushBdry_le_pushCyc (F.sc p) (𝟙 ((F.sc p).X₂))) (bdrySub_le_cycSub F p)
      (imageSubmodule_bdry_id F p) (imageSubmodule_cyc_id F p)

/-- The forward map of `homologySubqIso` is the forward map of `pushSubqIso` along the identity,
followed by the identification of the two equal subquotients. -/
lemma homologySubqIso_hom : (homologySubqIso F p).hom =
    (pushSubqIso (F.sc p) (𝟙 ((F.sc p).X₂)) (mono_id_modules ((F.sc p).X₂))).hom ≫
      subqMap (pushBdry_le_pushCyc (F.sc p) (𝟙 ((F.sc p).X₂))) (bdrySub_le_cycSub F p)
        (imageSubmodule_cyc_id F p).le (imageSubmodule_bdry_id F p).le := rfl

/-- **`H^p(𝓘^n𝓕^•)` is the subquotient `(Z ⊓ 𝓘^n𝓕^p) / d(𝓘^n𝓕^{p-1})` of `𝓕^p`.** -/
def cohIso (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n : ℕ) :
    S.cohomology n p ≅ subq (bdryPwSub I F p n) (cycSub F p ⊓ pwSub I F p n)
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) :=
  pushSubqIso ((S.complex n).sc p) ((S.inclusion n).f p)
    (mono_inclusion_f I F S n p) ≪≫
    subqEqIso (pushBdry_le_pushCyc ((S.complex n).sc p) ((S.inclusion n).f p))
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n)
      (imageSubmodule_bdry_inclusion I F p S n) (imageSubmodule_cyc_inclusion I F p S n)

/-- The forward map of `cohIso` is the forward map of `pushSubqIso` along the inclusion
`𝓘^n𝓕^p ⊆ 𝓕^p`, followed by the identification of the two equal subquotients. -/
lemma cohIso_hom (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n : ℕ) :
    (cohIso I F p S hF n).hom =
      (pushSubqIso ((S.complex n).sc p) ((S.inclusion n).f p)
          (mono_inclusion_f I F S n p)).hom ≫
        subqMap (pushBdry_le_pushCyc ((S.complex n).sc p) ((S.inclusion n).f p))
          (bdryPwSub_le_cycSub_inf_pwSub I F p hF n)
          (imageSubmodule_cyc_inclusion I F p S n).le
          (imageSubmodule_bdry_inclusion I F p S n).le := rfl

/-! ### The comparison maps as maps of subquotients -/

/-- The morphism of short complexes in degree `p` given by the inclusion `𝓘^n𝓕^• ⊆ 𝓕^•`. -/
def scInclusion (S : IdealPowerComplexSystem I F) (n : ℕ) : (S.complex n).sc p ⟶ F.sc p :=
  (HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) p).map (S.inclusion n)

/-- The morphism of short complexes in degree `p` given by `𝓘^(n+1)𝓕^• ⊆ 𝓘^n𝓕^•`. -/
def scTransition (S : IdealPowerComplexSystem I F) (n : ℕ) :
    (S.complex (n + 1)).sc p ⟶ (S.complex n).sc p :=
  (HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) p).map (S.transition n)

/-- The map `H^p(𝓘^n𝓕^•) ⟶ H^p(𝓕^•)` is the homology map of `scInclusion`. -/
lemma cohomologyToOriginal_eq (S : IdealPowerComplexSystem I F) (n : ℕ) :
    S.cohomologyToOriginal n p = ShortComplex.homologyMap (scInclusion I F p S n) := rfl

/-- The transition map `H^p(𝓘^(n+1)𝓕^•) ⟶ H^p(𝓘^n𝓕^•)` is the homology map of `scTransition`.
-/
lemma cohomologyTransition_eq (S : IdealPowerComplexSystem I F) (n : ℕ) :
    S.cohomologyTransition n p = ShortComplex.homologyMap (scTransition I F p S n) := rfl

/-- The map of subquotients `(Z ⊓ 𝓘^n𝓕^p)/d(𝓘^n𝓕^(p-1)) ⟶ Z/B` underlying
`H^p(𝓘^n𝓕^•) ⟶ H^p(𝓕^•)`. -/
def cohToHom (hF : TermsCoherent F) (n : ℕ) :
    subq (bdryPwSub I F p n) (cycSub F p ⊓ pwSub I F p n)
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) ⟶ homSub F p :=
  subqMap (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) (bdrySub_le_cycSub F p) inf_le_left
    (bdryPwSub_le_bdrySub I F p n)

/-- **Step 3.4 for the comparison with `𝓕^•`.** The canonical map
`H^p(𝓘^n𝓕^•) ⟶ H^p(𝓕^•)` is the map of subquotients of `𝓕^p`. -/
lemma cohomologyToOriginal_comp_homIso_hom (S : IdealPowerComplexSystem I F)
    (hF : TermsCoherent F) (n : ℕ) :
    S.cohomologyToOriginal n p ≫ (homologySubqIso F p).hom =
      (cohIso I F p S hF n).hom ≫ cohToHom I F p hF n := by
  refine (homologyMap_comp_pushSubqIso_hom_comp_subqMap _ _ (scInclusion I F p S n)
    ((S.inclusion n).f p) (mono_inclusion_f I F S n p) (𝟙 ((F.sc p).X₂))
    (mono_id_modules ((F.sc p).X₂)) (Category.comp_id _)
    ((imageSubmodule_bdry_inclusion I F p S n).le.trans
      ((bdryPwSub_le_bdrySub I F p n).trans (imageSubmodule_bdry_id F p).ge))
    ((imageSubmodule_cyc_inclusion I F p S n).le.trans
      (inf_le_left.trans (imageSubmodule_cyc_id F p).ge)) (bdrySub_le_cycSub F p)
    (imageSubmodule_cyc_id F p).le (imageSubmodule_bdry_id F p).le).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t)
    (subqMap_comp (pushBdry_le_pushCyc ((S.complex n).sc p) ((S.inclusion n).f p))
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) (bdrySub_le_cycSub F p)
      (imageSubmodule_cyc_inclusion I F p S n).le (imageSubmodule_bdry_inclusion I F p S n).le
      inf_le_left (bdryPwSub_le_bdrySub I F p n)))).symm

/-- In each degree the inclusion of `𝓘^(n+1)𝓕^•` factors through that of `𝓘^n𝓕^•`. -/
lemma transition_f_comp_inclusion_f (S : IdealPowerComplexSystem I F) (n : ℕ) (i : ℤ) :
    (S.transition n).f i ≫ (S.inclusion n).f i = (S.inclusion (n + 1)).f i :=
  congrArg (fun t : S.complex (n + 1) ⟶ F => t.f i) (S.transition_include n)

/-- **Step 3.4 for the transition maps.** The canonical map
`H^p(𝓘^(n+1)𝓕^•) ⟶ H^p(𝓘^n𝓕^•)` is the map of subquotients of `𝓕^p`. -/
lemma cohomologyTransition_comp_cohIso_hom (S : IdealPowerComplexSystem I F)
    (hF : TermsCoherent F) (n : ℕ) :
    S.cohomologyTransition n p ≫ (cohIso I F p S hF n).hom =
      (cohIso I F p S hF (n + 1)).hom ≫
        subqMap (bdryPwSub_le_cycSub_inf_pwSub I F p hF (n + 1))
          (bdryPwSub_le_cycSub_inf_pwSub I F p hF n)
          (inf_le_inf_left _ (pwSub_antitone I F p (Nat.le_succ n)))
          (bdryPwSub_antitone I F p (Nat.le_succ n)) := by
  refine (homologyMap_comp_pushSubqIso_hom_comp_subqMap _ _ (scTransition I F p S n)
    ((S.inclusion (n + 1)).f p) (mono_inclusion_f I F S (n + 1) p) ((S.inclusion n).f p)
    (mono_inclusion_f I F S n p) (transition_f_comp_inclusion_f I F S n p)
    ((imageSubmodule_bdry_inclusion I F p S (n + 1)).le.trans
      ((bdryPwSub_antitone I F p (Nat.le_succ n)).trans
        (imageSubmodule_bdry_inclusion I F p S n).ge))
    ((imageSubmodule_cyc_inclusion I F p S (n + 1)).le.trans
      ((inf_le_inf_left _ (pwSub_antitone I F p (Nat.le_succ n))).trans
        (imageSubmodule_cyc_inclusion I F p S n).ge))
    (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) (imageSubmodule_cyc_inclusion I F p S n).le
    (imageSubmodule_bdry_inclusion I F p S n).le).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t)
    (subqMap_comp (pushBdry_le_pushCyc ((S.complex (n + 1)).sc p) ((S.inclusion (n + 1)).f p))
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF (n + 1))
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n)
      (imageSubmodule_cyc_inclusion I F p S (n + 1)).le
      (imageSubmodule_bdry_inclusion I F p S (n + 1)).le
      (inf_le_inf_left _ (pwSub_antitone I F p (Nat.le_succ n)))
      (bdryPwSub_antitone I F p (Nat.le_succ n))))).symm

/-- The canonical map `H^p(𝓘^n𝓕^•) ⟶ H^p(𝓕^•)` in its subquotient form. -/
lemma cohomologyToOriginal_eq_conj (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F)
    (n : ℕ) : S.cohomologyToOriginal n p =
      (cohIso I F p S hF n).hom ≫ cohToHom I F p hF n ≫ (homologySubqIso F p).inv :=
  hom_conj_eq (cohIso I F p S hF n) (homologySubqIso F p) (cohToHom I F p hF n) _
    (cohomologyToOriginal_comp_homIso_hom I F p S hF n)

/-! ### The transition maps of the system `(H^p(𝓘^n𝓕^•))` -/

/-- Conjugates of composable maps compose to the conjugate of any map equal to their composite. -/
private lemma conj_comp_conj_eq {C : Type w} [Category.{v} C] {A A' B B' D D' : C}
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') {r : A' ⟶ B'} {s : B' ⟶ D'} {t : A' ⟶ D'}
    (h : r ≫ s = t) : (a.hom ≫ r ≫ b.inv) ≫ (b.hom ≫ s ≫ d.inv) = a.hom ≫ t ≫ d.inv := by
  subst h
  exact hom_conj_comp a b d r s

/-- The canonical map `H^p(𝓘^m𝓕^•) ⟶ H^p(𝓘^n𝓕^•)`, given the containments it is built from. -/
def tauMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (m n : ℕ)
    (hM : cycSub F p ⊓ pwSub I F p m ≤ cycSub F p ⊓ pwSub I F p n)
    (hN : bdryPwSub I F p m ≤ bdryPwSub I F p n) :
    S.cohomology m p ⟶ S.cohomology n p :=
  (cohIso I F p S hF m).hom ≫
    subqMap (bdryPwSub_le_cycSub_inf_pwSub I F p hF m)
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) hM hN ≫ (cohIso I F p S hF n).inv

/-- The canonical map `H^p(𝓘^n𝓕^•) ⟶ H^p(𝓘^n𝓕^•)` is the identity. -/
lemma tauMap_id (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n : ℕ)
    (hM : cycSub F p ⊓ pwSub I F p n ≤ cycSub F p ⊓ pwSub I F p n)
    (hN : bdryPwSub I F p n ≤ bdryPwSub I F p n) :
    tauMap I F p S hF n n hM hN = 𝟙 (S.cohomology n p) :=
  (congrArg (fun t => (cohIso I F p S hF n).hom ≫ t ≫ (cohIso I F p S hF n).inv)
      (subqMap_id (bdryPwSub_le_cycSub_inf_pwSub I F p hF n))).trans
    (hom_conj_id (cohIso I F p S hF n))

/-- The canonical maps compose: `H^p(𝓘^k𝓕^•) ⟶ H^p(𝓘^m𝓕^•) ⟶ H^p(𝓘^n𝓕^•)` is the canonical map
`H^p(𝓘^k𝓕^•) ⟶ H^p(𝓘^n𝓕^•)`. -/
lemma tauMap_comp (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (k m n : ℕ)
    (hM₁ : cycSub F p ⊓ pwSub I F p k ≤ cycSub F p ⊓ pwSub I F p m)
    (hN₁ : bdryPwSub I F p k ≤ bdryPwSub I F p m)
    (hM₂ : cycSub F p ⊓ pwSub I F p m ≤ cycSub F p ⊓ pwSub I F p n)
    (hN₂ : bdryPwSub I F p m ≤ bdryPwSub I F p n) :
    tauMap I F p S hF k m hM₁ hN₁ ≫ tauMap I F p S hF m n hM₂ hN₂ =
      tauMap I F p S hF k n (hM₁.trans hM₂) (hN₁.trans hN₂) :=
  conj_comp_conj_eq (cohIso I F p S hF k) (cohIso I F p S hF m) (cohIso I F p S hF n)
    (subqMap_comp _ _ _ hM₁ hN₁ hM₂ hN₂)

/-- The canonical map is the transition of the system. -/
lemma tauMap_succ (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n : ℕ) :
    tauMap I F p S hF (n + 1) n (inf_le_inf_left _ (pwSub_antitone I F p (Nat.le_succ n)))
        (bdryPwSub_antitone I F p (Nat.le_succ n)) = S.cohomologyTransition n p :=
  (hom_conj_eq (cohIso I F p S hF (n + 1)) (cohIso I F p S hF n) _ _
    (cohomologyTransition_comp_cohIso_hom I F p S hF n)).symm

/-- The canonical maps are compatible with the comparison to `H^p(𝓕^•)`. -/
lemma tauMap_comp_cohomologyToOriginal (S : IdealPowerComplexSystem I F)
    (hF : TermsCoherent F) (m n : ℕ)
    (hM : cycSub F p ⊓ pwSub I F p m ≤ cycSub F p ⊓ pwSub I F p n)
    (hN : bdryPwSub I F p m ≤ bdryPwSub I F p n) :
    tauMap I F p S hF m n hM hN ≫ S.cohomologyToOriginal n p =
      S.cohomologyToOriginal m p :=
  ((congrArg (fun t => tauMap I F p S hF m n hM hN ≫ t)
        (cohomologyToOriginal_eq_conj I F p S hF n)).trans
      (conj_comp_conj_eq (cohIso I F p S hF m) (cohIso I F p S hF n) (homologySubqIso F p)
        (subqMap_comp _ _ _ hM hN inf_le_left (bdryPwSub_le_bdrySub I F p n)))).trans
    (cohomologyToOriginal_eq_conj I F p S hF m).symm

/-! ### The ideal powers of `H^p(𝓕^•)` as subquotients of `𝓕^p` -/

/-- The forward map of an isomorphism of modules on a scheme is a monomorphism. -/
lemma mono_of_iso_hom_modules {M N : X.Modules} (e : M ≅ N) : Mono e.hom :=
  mono_of_injective_app_affine _ fun U => injective_secMap_of_isIso _ (isIso_hom_of_iso e) U.1

/-- An isomorphism of quasi-coherent modules identifies their ideal-power multiples. -/
def idealPowerTransferIso (m : ℕ) {M N : X.Modules} (e : M ≅ N) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) :
    ((Stacks.Algebraization.idealPowerMultiple I m M).toSheafOfModules : X.Modules) ≅
      ((Stacks.Algebraization.idealPowerMultiple I m N).toSheafOfModules : X.Modules) :=
  imageSubmoduleIso (subι (Stacks.Algebraization.idealPowerMultiple I m M) ≫ e.hom)
      (mono_subι_comp e.hom (mono_of_iso_hom_modules e)
        (Stacks.Algebraization.idealPowerMultiple I m M)) ≪≫
    submoduleEqIso (imageSubmodule_idealPowerMultiple_of_epi I m hM hN e.hom
      (epi_of_isIso_modules _ (isIso_hom_of_iso e)))

/-- Under `idealPowerTransferIso`, the inclusion `𝓘^mN ⊆ N` corresponds to the inclusion
`𝓘^mM ⊆ M` followed by `e`. -/
lemma idealPowerTransferIso_hom_comp_subι (m : ℕ) {M N : X.Modules} (e : M ≅ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (idealPowerTransferIso I m e hM hN).hom ≫
        subι (Stacks.Algebraization.idealPowerMultiple I m N) =
      subι (Stacks.Algebraization.idealPowerMultiple I m M) ≫ e.hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (imageSubmoduleIso
            (subι (Stacks.Algebraization.idealPowerMultiple I m M) ≫ e.hom)
            (mono_subι_comp e.hom (mono_of_iso_hom_modules e)
              (Stacks.Algebraization.idealPowerMultiple I m M))).hom ≫ t)
        (submoduleEqIso_hom_comp_subι (imageSubmodule_idealPowerMultiple_of_epi I m hM hN
          e.hom (epi_of_isIso_modules _ (isIso_hom_of_iso e))))).trans
      (imageSubmoduleIso_hom_comp_subι _ _))

/-- The homology of a complex of coherent modules is quasi-coherent. -/
lemma isQuasicoherent_homology (hF : TermsCoherent F) : (F.homology p).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (homologySubqIso F p).symm
    (isQuasicoherent_homSub F p hF)

/-- **`𝓘^m𝓗` is the subquotient `(𝓘^mZ)/(𝓘^mZ ⊓ B)` of `𝓕^p`.** -/
def idealPowerSubqIso (hF : TermsCoherent F) (m : ℕ) :
    ((Stacks.Algebraization.idealPowerMultiple I m (F.homology p)).toSheafOfModules :
        X.Modules) ≅
      subq (cycPwSub I F p m ⊓ bdrySub F p) (cycPwSub I F p m) inf_le_left :=
  idealPowerTransferIso I m (homologySubqIso F p) (isQuasicoherent_homology F p hF)
      (isQuasicoherent_homSub F p hF) ≪≫ (idealPowerHomIso I F p hF m).symm

/-- The forward map of `idealPowerSubqIso` is the forward map of `idealPowerTransferIso` followed
by the inverse of `idealPowerHomIso`. -/
lemma idealPowerSubqIso_hom (hF : TermsCoherent F) (m : ℕ) :
    (idealPowerSubqIso I F p hF m).hom =
      (idealPowerTransferIso I m (homologySubqIso F p) (isQuasicoherent_homology F p hF)
        (isQuasicoherent_homSub F p hF)).hom ≫ (idealPowerHomIso I F p hF m).inv := rfl

/-- The inverse of `idealPowerHomIso` followed by `homSubPwMap` is the inclusion `𝓘^m𝓗 ⊆ 𝓗`. -/
lemma idealPowerHomIso_inv_comp_homSubPwMap (hF : TermsCoherent F) (m : ℕ) :
    (idealPowerHomIso I F p hF m).inv ≫ homSubPwMap I F p m =
      subι (Stacks.Algebraization.idealPowerMultiple I m (homSub F p)) :=
  (congrArg (fun t => (idealPowerHomIso I F p hF m).inv ≫ t)
      (idealPowerHomIso_hom_comp_subι I F p hF m).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ subι (Stacks.Algebraization.idealPowerMultiple I m
          (homSub F p))) (idealPowerHomIso I F p hF m).inv_hom_id).trans
        (Category.id_comp _)))

/-- The inclusion `𝓘^m𝓗 ⊆ 𝓗` in subquotient form. -/
lemma subι_eq_conj (hF : TermsCoherent F) (m : ℕ) :
    subι (Stacks.Algebraization.idealPowerMultiple I m (F.homology p)) =
      (idealPowerSubqIso I F p hF m).hom ≫ homSubPwMap I F p m ≫ (homologySubqIso F p).inv :=
  hom_conj_eq (idealPowerSubqIso I F p hF m) (homologySubqIso F p) (homSubPwMap I F p m) _
    ((idealPowerTransferIso_hom_comp_subι I m (homologySubqIso F p)
        (isQuasicoherent_homology F p hF) (isQuasicoherent_homSub F p hF)).symm.trans
      (((congrArg (fun t => (idealPowerTransferIso I m (homologySubqIso F p)
              (isQuasicoherent_homology F p hF) (isQuasicoherent_homSub F p hF)).hom ≫ t)
            (idealPowerHomIso_inv_comp_homSubPwMap I F p hF m).symm).trans
          (Category.assoc _ _ _).symm).trans
        (congrArg (fun t => t ≫ homSubPwMap I F p m) (idealPowerSubqIso_hom I F p hF m).symm)))

/-- The inclusion `𝓘^m𝓗 ⊆ 𝓘^n𝓗` in subquotient form. -/
lemma subHom_eq_conj (hF : TermsCoherent F) {m n : ℕ} (h : n ≤ m) :
    subHom (idealPowerMultiple_antitone I (F.homology p) h) =
      (idealPowerSubqIso I F p hF m).hom ≫
        subqMap (inf_le_left : cycPwSub I F p m ⊓ bdrySub F p ≤ cycPwSub I F p m)
          (inf_le_left : cycPwSub I F p n ⊓ bdrySub F p ≤ cycPwSub I F p n)
          (cycPwSub_antitone I F p h)
          (inf_le_inf_right _ (cycPwSub_antitone I F p h)) ≫
        (idealPowerSubqIso I F p hF n).inv :=
  cancel_subι (Stacks.Algebraization.idealPowerMultiple I n (F.homology p)) _ _
    ((homOfLE_comp_subι (idealPowerMultiple_antitone I (F.homology p) h)).trans
      ((subι_eq_conj I F p hF m).trans
        ((conj_comp_conj_eq (idealPowerSubqIso I F p hF m) (idealPowerSubqIso I F p hF n)
            (homologySubqIso F p) (subqMap_comp inf_le_left inf_le_left (bdrySub_le_cycSub F p)
              (cycPwSub_antitone I F p h) (inf_le_inf_right _ (cycPwSub_antitone I F p h))
              (cycPwSub_le_cycSub I F p n) inf_le_right)).symm.trans
          (congrArg (fun t => ((idealPowerSubqIso I F p hF m).hom ≫
              subqMap (inf_le_left : cycPwSub I F p m ⊓ bdrySub F p ≤ cycPwSub I F p m)
                (inf_le_left : cycPwSub I F p n ⊓ bdrySub F p ≤ cycPwSub I F p n)
                (cycPwSub_antitone I F p h)
                (inf_le_inf_right _ (cycPwSub_antitone I F p h)) ≫
              (idealPowerSubqIso I F p hF n).inv) ≫ t) (subι_eq_conj I F p hF n).symm))))

/-! ### The Artin-Rees comparison maps -/

/-- Whenever the cycles in `𝓘^n𝓕^p` lie in `𝓘^aZ`, the boundaries `d(𝓘^n𝓕^(p-1))` lie in
`𝓘^aZ ⊓ B`. -/
lemma bdryPwSub_le_cycPwSub_inf_bdrySub (hF : TermsCoherent F) (n a : ℕ)
    (h : cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a) :
    bdryPwSub I F p n ≤ cycPwSub I F p a ⊓ bdrySub F p :=
  le_inf ((bdryPwSub_le_cycSub_inf_pwSub I F p hF n).trans h) (bdryPwSub_le_bdrySub I F p n)

/-- The comparison `H^p(𝓘^n𝓕^•) ⟶ 𝓘^a𝓗`, available once the cycles in `𝓘^n𝓕^p` lie in
`𝓘^aZ`. -/
def rhoMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n a : ℕ)
    (h : cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a) :
    S.cohomology n p ⟶
      ((Stacks.Algebraization.idealPowerMultiple I a (F.homology p)).toSheafOfModules :
        X.Modules) :=
  (cohIso I F p S hF n).hom ≫
    subqMap (bdryPwSub_le_cycSub_inf_pwSub I F p hF n)
      (inf_le_left : cycPwSub I F p a ⊓ bdrySub F p ≤ cycPwSub I F p a) h
      (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF n a h) ≫ (idealPowerSubqIso I F p hF a).inv

/-- The comparison `𝓘^n𝓗 ⟶ H^p(𝓘^b𝓕^•)`, available once `𝓘^nZ` lies in the cycles inside
`𝓘^b𝓕^p` and `𝓘^nZ ⊓ B` lies in `d(𝓘^b𝓕^(p-1))`. -/
def psiMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n b : ℕ)
    (hM : cycPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p b)
    (hN : cycPwSub I F p n ⊓ bdrySub F p ≤ bdryPwSub I F p b) :
    ((Stacks.Algebraization.idealPowerMultiple I n (F.homology p)).toSheafOfModules :
        X.Modules) ⟶ S.cohomology b p :=
  (idealPowerSubqIso I F p hF n).hom ≫
    subqMap (inf_le_left : cycPwSub I F p n ⊓ bdrySub F p ≤ cycPwSub I F p n)
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF b) hM hN ≫ (cohIso I F p S hF b).inv

/-- **The image of `H^p(𝓘^n𝓕^•) ⟶ 𝓗` lies in `𝓘^a𝓗`**: the comparison followed by the inclusion
of `𝓘^a𝓗` is the canonical map. -/
lemma rhoMap_comp_subι (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F) (n a : ℕ)
    (h : cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a) :
    rhoMap I F p S hF n a h ≫
        subι (Stacks.Algebraization.idealPowerMultiple I a (F.homology p)) =
      S.cohomologyToOriginal n p :=
  ((congrArg (fun t => rhoMap I F p S hF n a h ≫ t) (subι_eq_conj I F p hF a)).trans
      (conj_comp_conj_eq (cohIso I F p S hF n) (idealPowerSubqIso I F p hF a)
        (homologySubqIso F p)
        (subqMap_comp (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) inf_le_left
          (bdrySub_le_cycSub F p) h (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF n a h)
          (cycPwSub_le_cycSub I F p a) inf_le_right))).trans
    (cohomologyToOriginal_eq_conj I F p S hF n).symm

/-- **The comparison `𝓘^n𝓗 ⟶ H^p(𝓘^b𝓕^•)` is canonical**: composed with the map to `𝓗` it is the
inclusion of `𝓘^n𝓗`. -/
lemma psiMap_comp_cohomologyToOriginal (S : IdealPowerComplexSystem I F)
    (hF : TermsCoherent F) (n b : ℕ)
    (hM : cycPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p b)
    (hN : cycPwSub I F p n ⊓ bdrySub F p ≤ bdryPwSub I F p b) :
    psiMap I F p S hF n b hM hN ≫ S.cohomologyToOriginal b p =
      subι (Stacks.Algebraization.idealPowerMultiple I n (F.homology p)) :=
  ((congrArg (fun t => psiMap I F p S hF n b hM hN ≫ t)
        (cohomologyToOriginal_eq_conj I F p S hF b)).trans
      (conj_comp_conj_eq (idealPowerSubqIso I F p hF n) (cohIso I F p S hF b)
        (homologySubqIso F p)
        (subqMap_comp inf_le_left (bdryPwSub_le_cycSub_inf_pwSub I F p hF b)
          (bdrySub_le_cycSub F p) hM hN inf_le_left (bdryPwSub_le_bdrySub I F p b)))).trans
    (subι_eq_conj I F p hF n).symm

/-- **First round trip.** `H^p(𝓘^n𝓕^•) → 𝓘^a𝓗 → H^p(𝓘^b𝓕^•)` is the canonical map. -/
lemma rhoMap_comp_psiMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F)
    (n a b : ℕ) (h : cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a)
    (hM : cycPwSub I F p a ≤ cycSub F p ⊓ pwSub I F p b)
    (hN : cycPwSub I F p a ⊓ bdrySub F p ≤ bdryPwSub I F p b) :
    rhoMap I F p S hF n a h ≫ psiMap I F p S hF a b hM hN =
      tauMap I F p S hF n b (h.trans hM)
        ((bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF n a h).trans hN) :=
  conj_comp_conj_eq (cohIso I F p S hF n) (idealPowerSubqIso I F p hF a) (cohIso I F p S hF b)
    (subqMap_comp (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) inf_le_left
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF b) h
      (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF n a h) hM hN)

/-- **Second round trip.** `𝓘^n𝓗 → H^p(𝓘^b𝓕^•) → 𝓘^a𝓗` is the inclusion. -/
lemma psiMap_comp_rhoMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F)
    {n a : ℕ} (b : ℕ) (hle : a ≤ n)
    (hM : cycPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p b)
    (hN : cycPwSub I F p n ⊓ bdrySub F p ≤ bdryPwSub I F p b)
    (h : cycSub F p ⊓ pwSub I F p b ≤ cycPwSub I F p a) :
    psiMap I F p S hF n b hM hN ≫ rhoMap I F p S hF b a h =
      subHom (idealPowerMultiple_antitone I (F.homology p) hle) :=
  (conj_comp_conj_eq (idealPowerSubqIso I F p hF n) (cohIso I F p S hF b)
      (idealPowerSubqIso I F p hF a)
      (subqMap_comp inf_le_left (bdryPwSub_le_cycSub_inf_pwSub I F p hF b) inf_le_left
        hM hN h (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF b a h))).trans
    (subHom_eq_conj I F p hF hle).symm

/-- The comparison `H^p(𝓘^n𝓕^•) ⟶ 𝓘^a𝓗` is compatible with the transitions on both sides. -/
lemma tauMap_comp_rhoMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F)
    (m n : ℕ) {a a' : ℕ} (hle : a ≤ a')
    (hM : cycSub F p ⊓ pwSub I F p m ≤ cycSub F p ⊓ pwSub I F p n)
    (hN : bdryPwSub I F p m ≤ bdryPwSub I F p n)
    (h : cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a)
    (h' : cycSub F p ⊓ pwSub I F p m ≤ cycPwSub I F p a') :
    tauMap I F p S hF m n hM hN ≫ rhoMap I F p S hF n a h =
      rhoMap I F p S hF m a' h' ≫
        subHom (idealPowerMultiple_antitone I (F.homology p) hle) := by
  have hL := conj_comp_conj_eq (cohIso I F p S hF m) (cohIso I F p S hF n)
    (idealPowerSubqIso I F p hF a)
    (subqMap_comp (bdryPwSub_le_cycSub_inf_pwSub I F p hF m)
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF n) inf_le_left hM hN h
      (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF n a h))
  have hR := (congrArg (fun t => rhoMap I F p S hF m a' h' ≫ t)
      (subHom_eq_conj I F p hF hle)).trans
    (conj_comp_conj_eq (cohIso I F p S hF m) (idealPowerSubqIso I F p hF a')
      (idealPowerSubqIso I F p hF a)
      (subqMap_comp (bdryPwSub_le_cycSub_inf_pwSub I F p hF m) inf_le_left inf_le_left h'
        (bdryPwSub_le_cycPwSub_inf_bdrySub I F p hF m a' h') (cycPwSub_antitone I F p hle)
        (inf_le_inf_right _ (cycPwSub_antitone I F p hle))))
  exact hL.trans hR.symm

/-- The comparison `𝓘^n𝓗 ⟶ H^p(𝓘^b𝓕^•)` is compatible with the transitions on both sides. -/
lemma subHom_comp_psiMap (S : IdealPowerComplexSystem I F) (hF : TermsCoherent F)
    {m n : ℕ} (hle : n ≤ m) (b b' : ℕ)
    (hM : cycPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p b)
    (hN : cycPwSub I F p n ⊓ bdrySub F p ≤ bdryPwSub I F p b)
    (hM' : cycPwSub I F p m ≤ cycSub F p ⊓ pwSub I F p b')
    (hN' : cycPwSub I F p m ⊓ bdrySub F p ≤ bdryPwSub I F p b')
    (hMT : cycSub F p ⊓ pwSub I F p b' ≤ cycSub F p ⊓ pwSub I F p b)
    (hNT : bdryPwSub I F p b' ≤ bdryPwSub I F p b) :
    subHom (idealPowerMultiple_antitone I (F.homology p) hle) ≫
        psiMap I F p S hF n b hM hN =
      psiMap I F p S hF m b' hM' hN' ≫ tauMap I F p S hF b' b hMT hNT := by
  have hL := (congrArg (fun t => t ≫ psiMap I F p S hF n b hM hN)
      (subHom_eq_conj I F p hF hle)).trans
    (conj_comp_conj_eq (idealPowerSubqIso I F p hF m) (idealPowerSubqIso I F p hF n)
      (cohIso I F p S hF b)
      (subqMap_comp inf_le_left inf_le_left (bdryPwSub_le_cycSub_inf_pwSub I F p hF b)
        (cycPwSub_antitone I F p hle) (inf_le_inf_right _ (cycPwSub_antitone I F p hle)) hM hN))
  have hR := conj_comp_conj_eq (idealPowerSubqIso I F p hF m) (cohIso I F p S hF b')
    (cohIso I F p S hF b)
    (subqMap_comp inf_le_left (bdryPwSub_le_cycSub_inf_pwSub I F p hF b')
      (bdryPwSub_le_cycSub_inf_pwSub I F p hF b) hM' hN' hMT hNT)
  exact hL.trans hR.symm

/-! ### The pro-isomorphism -/

/-- **Stacks 0G4R, pro-isomorphism half.** Let `X` be a Noetherian scheme, `𝓘 ⊆ 𝒪_X` a
quasi-coherent sheaf of ideals and `𝓕^•` a complex of coherent `𝒪_X`-modules. Write
`𝓗 = H^p(𝓕^•)` and `𝓗_n = H^p(𝓘^n𝓕^•)`. There is a `c > 0` such that for `n ≥ c` the map
`𝓗_n → 𝓗` factors through `𝓘^(n-c)𝓗`, there is a canonical `𝓘^n𝓗 → 𝓗_(n-c)`, and the two
composites are the canonical maps; consequently `(𝓗_n)` and `(𝓘^n𝓗)` are isomorphic as
pro-objects, by the explicit cofinal shift `n ↦ n + c`. -/
@[stacks 0G4R "the pro-isomorphism half, for schemes, with no boundedness assumed on the complex:
the constant `c > 0`, the factorization of `H^p(𝓘^n𝓕^•) → H^p(𝓕^•)` through
`𝓘^(n-c)H^p(𝓕^•)` (the image containment), the canonical map `𝓘^nH^p(𝓕^•) → H^p(𝓘^(n-c)𝓕^•)`,
the two composites, and the resulting explicit isomorphism of pro-objects via the shift
`n ↦ n + c`. The canonical maps `… → H^p(𝓘^2𝓕^•) → H^p(𝓘𝓕^•) → H^p(𝓕^•)` that the tag asserts
first are the ones carried by `AlgebraicGeometry.IdealPowerComplexSystem`, constructed
unconditionally by `AlgebraicGeometry.idealPowerComplexSystem`."]
theorem cohomologyIdealPowers_proIsomorphic [IsNoetherian X]
    (hF : ∀ i : ℤ, _root_.SheafOfModules.IsCoherent (F.X i))
    (S : IdealPowerComplexSystem I F) :
    ∃ (τ : ∀ m n : ℕ, n ≤ m → (S.cohomology m p ⟶ S.cohomology n p)),
      (∀ n : ℕ, τ n n le_rfl = 𝟙 (S.cohomology n p)) ∧
      (∀ (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m),
        τ k m hkm ≫ τ m n hmn = τ k n (hmn.trans hkm)) ∧
      (∀ n : ℕ, τ (n + 1) n (Nat.le_succ n) = S.cohomologyTransition n p) ∧
      (∀ (m n : ℕ) (hmn : n ≤ m),
        τ m n hmn ≫ S.cohomologyToOriginal n p = S.cohomologyToOriginal m p) ∧
      ∃ c : ℕ, 0 < c ∧
        ∃ (ρ : ∀ n : ℕ, c ≤ n → (S.cohomology n p ⟶
                ((Stacks.Algebraization.idealPowerMultiple I (n - c)
                  (F.homology p)).toSheafOfModules : X.Modules)))
          (ψ : ∀ n : ℕ, c ≤ n →
                (((Stacks.Algebraization.idealPowerMultiple I n
                  (F.homology p)).toSheafOfModules : X.Modules) ⟶ S.cohomology (n - c) p)),
          (∀ (n : ℕ) (hn : c ≤ n), ρ n hn ≫
              subι (Stacks.Algebraization.idealPowerMultiple I (n - c) (F.homology p)) =
            S.cohomologyToOriginal n p) ∧
          (∀ (n : ℕ) (hn : c ≤ n), ψ n hn ≫ S.cohomologyToOriginal (n - c) p =
            subι (Stacks.Algebraization.idealPowerMultiple I n (F.homology p))) ∧
          (∀ (m n : ℕ) (hmn : n ≤ m) (hm : c ≤ m) (hn : c ≤ n),
            τ m n hmn ≫ ρ n hn = ρ m hm ≫
              subHom (idealPowerMultiple_antitone I (F.homology p)
                (Nat.sub_le_sub_right hmn c))) ∧
          (∀ (m n : ℕ) (hmn : n ≤ m) (hm : c ≤ m) (hn : c ≤ n),
            subHom (idealPowerMultiple_antitone I (F.homology p) hmn) ≫ ψ n hn =
              ψ m hm ≫ τ (m - c) (n - c) (Nat.sub_le_sub_right hmn c)) ∧
          (∀ (n : ℕ) (hn : 2 * c ≤ n),
            ρ n (by omega) ≫ ψ (n - c) (by omega) = τ n (n - c - c) (by omega)) ∧
          (∀ (n : ℕ) (hn : 2 * c ≤ n),
            ψ n (by omega) ≫ ρ (n - c) (by omega) =
              subHom (idealPowerMultiple_antitone I (F.homology p)
                (show n - c - c ≤ n by omega))) ∧
          ∃ (forward : ∀ m : ℕ, (S.cohomology (m + c) p ⟶
                  ((Stacks.Algebraization.idealPowerMultiple I m
                    (F.homology p)).toSheafOfModules : X.Modules)))
            (backward : ∀ m : ℕ,
                  (((Stacks.Algebraization.idealPowerMultiple I (m + c)
                    (F.homology p)).toSheafOfModules : X.Modules) ⟶ S.cohomology m p)),
            (∀ m : ℕ, forward m ≫
                subι (Stacks.Algebraization.idealPowerMultiple I m (F.homology p)) =
              S.cohomologyToOriginal (m + c) p) ∧
            (∀ m : ℕ, backward m ≫ S.cohomologyToOriginal m p =
              subι (Stacks.Algebraization.idealPowerMultiple I (m + c) (F.homology p))) ∧
            (∀ (m m' : ℕ) (h : m ≤ m'),
              τ (m' + c) (m + c) (Nat.add_le_add_right h c) ≫ forward m =
                forward m' ≫ subHom (idealPowerMultiple_antitone I (F.homology p) h)) ∧
            (∀ (m m' : ℕ) (h : m ≤ m'),
              subHom (idealPowerMultiple_antitone I (F.homology p)
                  (Nat.add_le_add_right h c)) ≫ backward m = backward m' ≫ τ m' m h) ∧
            (∀ m : ℕ, forward (m + c) ≫ backward m =
              τ (m + c + c) m (by omega)) ∧
            (∀ m : ℕ, backward (m + c) ≫ forward m =
              subHom (idealPowerMultiple_antitone I (F.homology p)
                (show m ≤ m + c + c by omega))) := by
  obtain ⟨c, hcpos, hAR1, hAR2⟩ := exists_artinRees_degree I F p hF
  have hAR : ∀ n a : ℕ, a + c ≤ n → cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p a :=
    fun n a ha => (hAR1 n (by omega)).trans (cycPwSub_antitone I F p (by omega))
  have hcyc : ∀ n b : ℕ, b ≤ n → cycPwSub I F p n ≤ cycSub F p ⊓ pwSub I F p b :=
    fun n b hb => le_inf (cycPwSub_le_cycSub I F p n)
      ((cycPwSub_le_pwSub I F p hF n).trans (pwSub_antitone I F p hb))
  have hbdy : ∀ n b : ℕ, b + c ≤ n →
      cycPwSub I F p n ⊓ bdrySub F p ≤ bdryPwSub I F p b :=
    fun n b hb => ((le_inf inf_le_right
        (inf_le_left.trans (cycPwSub_le_pwSub I F p hF n))).trans (hAR2 n (by omega))).trans
      (bdryPwSub_antitone I F p (by omega))
  refine ⟨fun m n h => tauMap I F p S hF m n (inf_le_inf_left _ (pwSub_antitone I F p h))
      (bdryPwSub_antitone I F p h), ?_, ?_, ?_, ?_, c, hcpos,
    fun n hn => rhoMap I F p S hF n (n - c) (hAR n (n - c) (by omega)),
    fun n hn => psiMap I F p S hF n (n - c) (hcyc n (n - c) (by omega))
      (hbdy n (n - c) (by omega)),
    ?_, ?_, ?_, ?_, ?_, ?_,
    fun m => rhoMap I F p S hF (m + c) m (hAR (m + c) m (by omega)),
    fun m => psiMap I F p S hF (m + c) m (hcyc (m + c) m (by omega))
      (hbdy (m + c) m (by omega)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => tauMap_id I F p S hF n _ _
  · exact fun k m n hkm hmn => tauMap_comp I F p S hF k m n _ _ _ _
  · exact fun n => tauMap_succ I F p S hF n
  · exact fun m n hmn => tauMap_comp_cohomologyToOriginal I F p S hF m n _ _
  · exact fun n hn => rhoMap_comp_subι I F p S hF n (n - c) _
  · exact fun n hn => psiMap_comp_cohomologyToOriginal I F p S hF n (n - c) _ _
  · exact fun m n hmn hm hn =>
      tauMap_comp_rhoMap I F p S hF m n (Nat.sub_le_sub_right hmn c) _ _ _ _
  · exact fun m n hmn hm hn =>
      subHom_comp_psiMap I F p S hF hmn (n - c) (m - c) _ _ _ _ _ _
  · exact fun n hn => rhoMap_comp_psiMap I F p S hF n (n - c) (n - c - c) _ _ _
  · exact fun n hn => psiMap_comp_rhoMap I F p S hF (n - c) (by omega) _ _ _
  · exact fun m => rhoMap_comp_subι I F p S hF (m + c) m _
  · exact fun m => psiMap_comp_cohomologyToOriginal I F p S hF (m + c) m _ _
  · exact fun m m' h => tauMap_comp_rhoMap I F p S hF (m' + c) (m + c) h _ _ _ _
  · exact fun m m' h =>
      subHom_comp_psiMap I F p S hF (Nat.add_le_add_right h c) m m' _ _ _ _ _ _
  · exact fun m => rhoMap_comp_psiMap I F p S hF (m + c + c) (m + c) m _ _ _
  · exact fun m => psiMap_comp_rhoMap I F p S hF (m + c) (by omega) _ _ _

end Stacks.Duality

end
