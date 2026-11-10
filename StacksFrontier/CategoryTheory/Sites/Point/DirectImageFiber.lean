module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransportGerm
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The stalk of a direct image at a point identified along a morphism of topoi

Let `g : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `Φ` a point of the site `C` and `Ψ` a point
of the site `D`, together with an identification `e : Ψ⁻¹ ≅ g⁻¹ ⋙ Φ⁻¹` of their stalk functors
on sheaves of sets — the situation of Stacks 05V1, in which `Ψ` is the image of `Φ` under `g`.
For a sheaf of sets `F` on `C` there is then a canonical map

`(g_*F)_Ψ ⟶ F_Φ`,

the identification `(g_*F)_Ψ = (g⁻¹g_*F)_Φ` followed by the stalk at `Φ` of the counit
`g⁻¹g_*F ⟶ F`. This file constructs it, natural in `F`, and proves two of its properties: on
the stalk of a morphism into a direct image it is the stalk of the transpose, and the
identification `e` carries pairs of elements of stalks to pairs.

## Main definitions

* `MorphismOfTopoi.pushforwardFiberMap`: the natural map `(g_*F)_Ψ ⟶ F_Φ`.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberCompToPi`: for a functor
  `u : C ⥤ D` and points `Φ i` of `D` whose fibres pulled back along `u` are identified with the
  fibre of a point `Ψ` of `C`, the map from the stalk at `Ψ` of `u_*P` to `∏ᵢ P_{Φ i}`.

## Main results

* `MorphismOfTopoi.pushforwardFiberMap_app_map`: applied to the stalk at `Ψ` of a morphism
  `P ⟶ g_*F`, the canonical map is the stalk at `Φ` of its transpose `g⁻¹P ⟶ F`, read through
  `e`.
* `MorphismOfTopoi.map_prodComparison_app`: through the product comparison of `g⁻¹`, the
  identification `e` carries a pair to the pair of its components.
* `CategoryTheory.GrothendieckTopology.Point.prodObjMk_toPresheafFiber`: the pair of the germs
  of two sections is the germ of the pair.
* `CategoryTheory.GrothendieckTopology.Point.bijective_presheafFiberCompToPi`: the stalk of a
  direct image is the product of the stalks, as soon as neighbourhoods of the points `Φ i`
  over `u V` can be refined to partitions of `u V'` for smaller neighbourhoods `V'` of `Ψ`.
* `CategoryTheory.GrothendieckTopology.Point.bijective_pushforwardFiberMap_iff`: for the
  identification of stalks along an adjunction `g⁻¹ ⊣ u_*`, the canonical maps
  `(g_*F)_Ψ ⟶ F_{Φ i}` assemble to a bijection exactly when `presheafFiberCompToPi` is one.

## Implementation notes

The criterion `bijective_presheafFiberCompToPi` is the site-theoretic skeleton of the proof of
Stacks 03QP and Stacks 0DK3: injectivity because two sections agreeing near every `Φ i` agree on
a covering of `u V'`, surjectivity because germs at the `Φ i` are glued along a partition.

## References

* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w₂ v u v' u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] [LocallySmall.{w} D] {K : GrothendieckTopology D}
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (Φ : J.Point.{w}) (Ψ : K.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅ g.inverseImage ⋙ Φ.sheafFiber (A := Type w))

/-- The canonical map from the stalk at `Ψ` of a direct image to the stalk at `Φ`. -/
def pushforwardFiberMap : g.pushforward ⋙ Ψ.sheafFiber (A := Type w) ⟶ Φ.sheafFiber where
  app F := e.hom.app (g.pushforward.obj F) ≫ Φ.sheafFiber.map (g.adj.counit.app F)
  naturality F G α := by
    have h₁ := e.hom.naturality (g.pushforward.map α)
    have h₂ := g.adj.counit.naturality α
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h₁ h₂ ⊢
    rw [Category.assoc, ← Φ.sheafFiber.map_comp, ← h₂, Φ.sheafFiber.map_comp,
      ← Category.assoc, ← Category.assoc, h₁]

omit [LocallySmall.{w} C] [LocallySmall.{w} D] in
/-- The component at `F` of `pushforwardFiberMap` is `e` at `g_*F` followed by the stalk at `Φ`
of the counit `g⁻¹g_*F ⟶ F`. -/
lemma pushforwardFiberMap_app (F : Sheaf J (Type w)) :
    (g.pushforwardFiberMap Φ Ψ e).app F =
      e.hom.app (g.pushforward.obj F) ≫ Φ.sheafFiber.map (g.adj.counit.app F) := rfl

omit [LocallySmall.{w} C] [LocallySmall.{w} D] in
/-- The canonical map applied to the stalk of a morphism into a direct image is the stalk of
its transpose. -/
lemma pushforwardFiberMap_app_map {P : Sheaf K (Type w)} {F : Sheaf J (Type w)}
    (β : P ⟶ g.pushforward.obj F) (z : Ψ.sheafFiber.obj P) :
    (g.pushforwardFiberMap Φ Ψ e).app F (Ψ.sheafFiber.map β z) =
      Φ.sheafFiber.map ((g.adj.homEquiv _ _).symm β) (e.hom.app P z) := by
  rw [pushforwardFiberMap_app, Adjunction.homEquiv_counit, Functor.map_comp]
  have h := ConcreteCategory.congr_hom (e.hom.naturality β) z
  simp only [Functor.comp_map, types_comp_apply] at h ⊢
  rw [h]

omit [LocallySmall.{w} D] in
/-- The identification of stalks carries pairs to pairs. -/
lemma map_prodComparison_app [PreservesFiniteLimits g.inverseImage] (P Q : Sheaf K (Type w))
    (z : Ψ.sheafFiber.obj (P ⨯ Q)) :
    Φ.sheafFiber.map (prodComparison g.inverseImage P Q) (e.hom.app (P ⨯ Q) z) =
      Functor.prodObjMk (P := Φ.sheafFiber (A := Type w))
        (e.hom.app P (Ψ.sheafFiber.map (prod.fst : P ⨯ Q ⟶ P) z))
        (e.hom.app Q (Ψ.sheafFiber.map (prod.snd : P ⨯ Q ⟶ Q) z)) := by
  rw [Functor.map_prodComparison_apply]
  congr 1
  · exact (ConcreteCategory.congr_hom (e.hom.naturality prod.fst) z).symm
  · exact (ConcreteCategory.congr_hom (e.hom.naturality prod.snd) z).symm

omit [LocallySmall.{w} D] in
/-- The stalk at `Φ` of the transpose of a morphism `P ⨯ Q ⟶ g_*E` of the form
`g.adj.homEquiv (prodComparison ≫ q)`, on the germ of a pair. -/
lemma map_homEquiv_symm_homEquiv_prodComparison_comp [PreservesFiniteLimits g.inverseImage]
    {P Q : Sheaf K (Type w)} {E : Sheaf J (Type w)}
    (q : g.inverseImage.obj P ⨯ g.inverseImage.obj Q ⟶ E) (z : Ψ.sheafFiber.obj (P ⨯ Q)) :
    Φ.sheafFiber.map ((g.adj.homEquiv _ _).symm
        (g.adj.homEquiv _ _ (prodComparison g.inverseImage P Q ≫ q))) (e.hom.app (P ⨯ Q) z) =
      Φ.sheafFiber.map q (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w))
        (e.hom.app P (Ψ.sheafFiber.map (prod.fst : P ⨯ Q ⟶ P) z))
        (e.hom.app Q (Ψ.sheafFiber.map (prod.snd : P ⨯ Q ⟶ Q) z))) := by
  rw [Equiv.symm_apply_apply, Functor.map_comp, types_comp_apply, map_prodComparison_app]

end MorphismOfTopoi

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w})

/-- The germ of a pair of sections is the pair of germs. -/
lemma prodObjMk_toPresheafFiber {P Q : Sheaf J (Type w)} (U : C) (x : Φ.fiber.obj U)
    (a : P.obj.obj (op U)) (b : Q.obj.obj (op U)) :
    Functor.prodObjMk (P := Φ.sheafFiber (A := Type w))
        (Φ.toPresheafFiber U x P.obj a) (Φ.toPresheafFiber U x Q.obj b) =
      Φ.toPresheafFiber U x (P ⨯ Q).obj
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor J (op U)) a b) := by
  refine Functor.prodObjMk_ext ?_ ?_
  · refine (Functor.map_fst_prodObjMk _ _).trans ?_
    refine Eq.trans ?_ (Φ.toPresheafFiber_naturality_apply (prod.fst : P ⨯ Q ⟶ P).hom U x _).symm
    exact congrArg _ (Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor J (op U)) a b).symm
  · refine (Functor.map_snd_prodObjMk _ _).trans ?_
    refine Eq.trans ?_ (Φ.toPresheafFiber_naturality_apply (prod.snd : P ⨯ Q ⟶ Q).hom U x _).symm
    exact congrArg _ (Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor J (op U)) a b).symm

end CategoryTheory.GrothendieckTopology.Point

/-! ### The stalk of a direct image along a functor of sites -/

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (uf : C ⥤ D) (Psi : J.Point.{w}) {ι : Type w} (Phi : ι → K.Point.{w})
  (ε : ∀ i, Psi.fiber ≅ uf ⋙ (Phi i).fiber)

/-- The legs of `presheafFiberCompToPi`. -/
def presheafFiberCompToPiLeg (P : Dᵒᵖ ⥤ Type (max w w₂)) (V : C) (t : Psi.fiber.obj V) :
    (uf.op ⋙ P).obj (op V) ⟶ ∀ i, (Phi i).presheafFiber.obj P :=
  TypeCat.ofHom fun s i => (Phi i).toPresheafFiber (uf.obj V) ((ε i).hom.app V t) P s

/-- The legs of `presheafFiberCompToPi` are compatible with restriction along `g : V ⟶ V'`. -/
lemma presheafFiberCompToPiLeg_w (P : Dᵒᵖ ⥤ Type (max w w₂)) ⦃V V' : C⦄ (g : V ⟶ V')
    (t : Psi.fiber.obj V) :
    (uf.op ⋙ P).map g.op ≫ presheafFiberCompToPiLeg uf Psi Phi ε P V t =
      presheafFiberCompToPiLeg uf Psi Phi ε P V' (Psi.fiber.map g t) := by
  ext s i
  have h := (Phi i).toPresheafFiber_w_apply (uf.map g) ((ε i).hom.app V t) P s
  have hn := ConcreteCategory.congr_hom ((ε i).hom.naturality g) t
  simp only [Functor.comp_map, types_comp_apply] at hn
  change (Phi i).toPresheafFiber (uf.obj V) ((ε i).hom.app V t) P (P.map (uf.map g).op s) =
    (Phi i).toPresheafFiber (uf.obj V') ((ε i).hom.app V' (Psi.fiber.map g t)) P s
  rw [hn]
  exact h

/-- The canonical map from the stalk at `Psi` of the direct image `uf_*P` of a presheaf of sets
to the product of its stalks at the points `Phi i`, each identified with `Psi` along `uf`: the
germ of a section `s` of `P` over `uf V` at `(V, t)` goes to the family of its germs at
`(uf V, ε i t)`. -/
def presheafFiberCompToPi (P : Dᵒᵖ ⥤ Type (max w w₂)) :
    Psi.presheafFiber.obj (uf.op ⋙ P) ⟶ ∀ i, (Phi i).presheafFiber.obj P :=
  Psi.presheafFiberDesc (presheafFiberCompToPiLeg uf Psi Phi ε P)
    (presheafFiberCompToPiLeg_w uf Psi Phi ε P)

/-- The component at `i` of `presheafFiberCompToPi` sends the germ of `s` at `(V, t)` to the germ
of `s` at `(uf V, ε i t)`. -/
lemma presheafFiberCompToPi_toPresheafFiber (P : Dᵒᵖ ⥤ Type (max w w₂)) (V : C)
    (t : Psi.fiber.obj V) (s : P.obj (op (uf.obj V))) (i : ι) :
    presheafFiberCompToPi uf Psi Phi ε P (Psi.toPresheafFiber V t (uf.op ⋙ P) s) i =
      (Phi i).toPresheafFiber (uf.obj V) ((ε i).hom.app V t) P s :=
  congrFun (ConcreteCategory.congr_hom (Psi.toPresheafFiber_presheafFiberDesc (P := uf.op ⋙ P)
    (presheafFiberCompToPiLeg uf Psi Phi ε P) (presheafFiberCompToPiLeg_w uf Psi Phi ε P) V t) s) i

section

variable [LocallySmall.{w} C] [LocallySmall.{w} D]

/-- **The stalk of a direct image is the product of the stalks.** Suppose the neighbourhoods of
the points `Phi i` lifted from `Psi` can be refined to partitions: whenever neighbourhoods `W i`
of the points `Phi i` over `uf V` are given, some smaller neighbourhood `V'` of `Psi` has `uf V'`
covered by pairwise disjoint subobjects `N i`, each a neighbourhood of `Phi i` mapping to `W i`
over `uf V`. Then for every sheaf of sets `P`, valued in any universe containing that of the
points, the stalk at `Psi` of `uf_* P` is the product of the stalks of `P` at the points `Phi i`,
by `presheafFiberCompToPi`. -/
theorem bijective_presheafFiberCompToPi (P : Sheaf K (Type (max w w₂)))
    (hglue : ∀ (V : C) (t : Psi.fiber.obj V) (W : ι → D) (w : ∀ i, (Phi i).fiber.obj (W i))
      (a : ∀ i, W i ⟶ uf.obj V), (∀ i, (Phi i).fiber.map (a i) (w i) = (ε i).hom.app V t) →
      ∃ (V' : C) (t' : Psi.fiber.obj V') (g : V' ⟶ V) (N : ι → D)
        (n : ∀ i, (Phi i).fiber.obj (N i)) (c : ∀ i, N i ⟶ uf.obj V') (b : ∀ i, N i ⟶ W i),
        Psi.fiber.map g t' = t ∧ (∀ i, c i ≫ uf.map g = b i ≫ a i) ∧
        (∀ i, (Phi i).fiber.map (c i) (n i) = (ε i).hom.app V' t') ∧
        (∀ i, (Phi i).fiber.map (b i) (n i) = w i) ∧
        Sieve.ofArrows N c ∈ K (uf.obj V') ∧ (∀ i, Mono (c i)) ∧
        (∀ i j, i ≠ j → ∀ (T : D) (p : T ⟶ N i) (q : T ⟶ N j), p ≫ c i = q ≫ c j →
          (⊥ : Sieve T) ∈ K T)) :
    Function.Bijective (presheafFiberCompToPi uf Psi Phi ε P.obj) := by
  classical
  constructor
  · intro z z' h
    obtain ⟨V, t, s, s', rfl, rfl⟩ :=
      Psi.toPresheafFiber_jointly_surjective₂ (P := uf.op ⋙ P.obj) z z'
    have hi : ∀ i, ∃ (Y : D) (f : Y ⟶ uf.obj V) (y : (Phi i).fiber.obj Y),
        (Phi i).fiber.map f y = (ε i).hom.app V t ∧ P.obj.map f.op s = P.obj.map f.op s' :=
      fun i => ((Phi i).toPresheafFiber_eq_iff' _ _ _ _).1 <| by
        simpa only [presheafFiberCompToPi_toPresheafFiber] using congrFun h i
    choose W a w hw heq using hi
    obtain ⟨V', t', g, N, -, c, b, hg, hcomm, -, -, hcov, -, -⟩ := hglue V t W w a hw
    have hle : Sieve.ofArrows N c ≤ Sieve.pullback (uf.map g) (Sieve.ofArrows W a) := by
      rintro T h ⟨Y, k, f, ⟨i⟩, rfl⟩
      change Sieve.ofArrows W a ((k ≫ c i) ≫ uf.map g)
      rw [Category.assoc, hcomm i, ← Category.assoc]
      exact ⟨_, k ≫ b i, a i, ⟨i⟩, rfl⟩
    have hs : P.obj.map (uf.map g).op s = P.obj.map (uf.map g).op s' := by
      refine ((isSheaf_iff_isSheaf_of_type _ _).1 P.property _
        (K.superset_covering hle hcov)).isSeparatedFor.ext fun T h hh => ?_
      obtain ⟨Y, k, f, ⟨i⟩, hk⟩ := hh
      simp only [← Functor.map_comp_apply, ← op_comp]
      rw [← hk, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, heq i]
    rw [← hg, ← Psi.toPresheafFiber_w_apply, ← Psi.toPresheafFiber_w_apply]
    exact congrArg _ hs
  · intro f
    choose W w s hs using fun i => (Phi i).toPresheafFiber_jointly_surjective (P := P.obj) (f i)
    obtain ⟨@⟨V₀, t₀⟩⟩ : Nonempty Psi.fiber.Elements := IsCofiltered.nonempty
    let A (i : ι) : (Phi i).fiber.Elements := (Phi i).fiber.elementsMk (W i) (w i)
    let A' (i : ι) : (Phi i).fiber.Elements :=
      (Phi i).fiber.elementsMk (uf.obj V₀) ((ε i).hom.app V₀ t₀)
    let E (i : ι) : (Phi i).fiber.Elements := IsCofiltered.min (A i) (A' i)
    let l (i : ι) : E i ⟶ A i := IsCofiltered.minToLeft (A i) (A' i)
    let r (i : ι) : E i ⟶ A' i := IsCofiltered.minToRight (A i) (A' i)
    obtain ⟨V', t', -, N, n, c, b, -, -, hc, hb, hcov, hmono, hdis⟩ := hglue V₀ t₀
      (fun i => (E i).1) (fun i => (E i).2) (fun i => (r i).1) (fun i => (r i).2)
    let x (i : ι) : PUnit.{max w w₂ + 1} ⟶ P.obj.obj (op (N i)) := TypeCat.ofHom fun _ =>
      P.obj.map (b i ≫ (l i).1).op (s i)
    have hx : ∀ ⦃T : D⦄ ⦃i j : ι⦄ (p : T ⟶ N i) (q : T ⟶ N j), p ≫ c i = q ≫ c j →
        x i ≫ P.obj.map p.op = x j ≫ P.obj.map q.op := by
      intro T i j p q hpq
      by_cases hij : i = j
      · subst hij
        rw [(cancel_mono _).1 hpq]
      · ext u
        exact ((isSheaf_iff_isSheaf_of_type _ _).1 P.property _
          (hdis i j hij T p q hpq)).isSeparatedFor.ext (fun _ _ h => h.elim)
    obtain ⟨σ, hσ, -⟩ := P.property.existsUnique_amalgamation_ofArrows c hcov x hx
    refine ⟨Psi.toPresheafFiber V' t' (uf.op ⋙ P.obj) (σ PUnit.unit), funext fun i => ?_⟩
    rw [presheafFiberCompToPi_toPresheafFiber, ← hc i, ← (Phi i).toPresheafFiber_w_apply]
    have hσi := ConcreteCategory.congr_hom (hσ i) PUnit.unit
    simp only [types_comp_apply] at hσi
    rw [hσi, ← hs i]
    change (Phi i).toPresheafFiber (N i) (n i) P.obj (P.obj.map (b i ≫ _).op (s i)) = _
    rw [(Phi i).toPresheafFiber_w_apply, Functor.map_comp_apply, hb i]
    exact congrArg (fun z => (Phi i).toPresheafFiber (W i) z P.obj (s i)) (l i).2

end

section Transport

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
  (uf : C ⥤ D) [uf.IsContinuous J K] (Psi : J.Point.{u}) {ι : Type u} (Phi : ι → K.Point.{u})
  (ε : ∀ i, Psi.fiber ≅ uf ⋙ (Phi i).fiber)
  (g : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))
  (β : g.pushforward ≅ uf.sheafPushforwardContinuous (Type u) J K)

/-- Let `g` be a morphism of topoi whose direct image is identified by `β` with the direct image
`uf_*` along a continuous functor `uf`. For the identification of stalks
`Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj` along the adjunction `g⁻¹ ⊣ uf_*`, the
canonical map `(g_*M)_Ψ ⟶ M_{Φ i}` is, once `g_*M` is read as `uf_*M` through `β`, the
component at `i` of `presheafFiberCompToPi`. -/
lemma pushforwardFiberMap_app_map_inv_eq (M : Sheaf K (Type u))
    (z : Psi.sheafFiber.obj ((uf.sheafPushforwardContinuous (Type u) J K).obj M)) (i : ι) :
    (g.pushforwardFiberMap (Phi i) Psi (Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj
        (Phi i) uf (g.adj.ofNatIsoRight β) Psi (ε i))).app M
        (Psi.sheafFiber.map (β.inv.app M) z) =
      presheafFiberCompToPi uf Psi Phi ε M.obj z i := by
  rw [MorphismOfTopoi.pushforwardFiberMap_app_map]
  have hc : (g.adj.homEquiv _ _).symm (β.inv.app M) = (g.adj.ofNatIsoRight β).counit.app M := by
    rw [← Adjunction.homEquiv_symm_id, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
      Category.id_comp]
  rw [hc]
  obtain ⟨V, t, s, rfl⟩ := Psi.toPresheafFiber_jointly_surjective
    (P := ((uf.sheafPushforwardContinuous (Type u) J K).obj M).obj) z
  exact (Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj_hom_app_counit_toPresheafFiber
    (Phi i) uf (g.adj.ofNatIsoRight β) Psi (ε i) M V t s).trans
    (presheafFiberCompToPi_toPresheafFiber uf Psi Phi ε M.obj V t s i).symm

/-- **Bijectivity of the stalk comparison of a direct image, transported.** In the situation of
`pushforwardFiberMap_app_map_inv_eq`, the canonical maps `(g_*M)_Ψ ⟶ M_{Φ i}` assemble to a
bijection `(g_*M)_Ψ ⟶ ∏ᵢ M_{Φ i}` exactly when `presheafFiberCompToPi` is a bijection. -/
lemma bijective_pushforwardFiberMap_iff (M : Sheaf K (Type u)) :
    Function.Bijective (fun (z : Psi.sheafFiber.obj (g.pushforward.obj M)) i =>
      (g.pushforwardFiberMap (Phi i) Psi (Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj
        (Phi i) uf (g.adj.ofNatIsoRight β) Psi (ε i))).app M z) ↔
      Function.Bijective (presheafFiberCompToPi uf Psi Phi ε M.obj) := by
  have hb : Function.Bijective (Psi.sheafFiber.map (β.inv.app M)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have heq : (fun (z : Psi.sheafFiber.obj (g.pushforward.obj M)) i =>
      (g.pushforwardFiberMap (Phi i) Psi (Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj
        (Phi i) uf (g.adj.ofNatIsoRight β) Psi (ε i))).app M z) ∘
        (Psi.sheafFiber.map (β.inv.app M)) =
      presheafFiberCompToPi uf Psi Phi ε M.obj :=
    funext fun z => funext fun i => pushforwardFiberMap_app_map_inv_eq uf Psi Phi ε g β M z i
  rw [← heq]
  exact ⟨fun h => h.comp hb, fun h => (Function.Bijective.of_comp_iff _ hb).1 h⟩

end Transport

end CategoryTheory.GrothendieckTopology.Point
