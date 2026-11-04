module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-! # Separatedness of the `Isom` sheaf of a stack in groupoids

Let `(𝒞, J)` be a site, let `q : 𝒴 ⥤ 𝒞` be a stack in groupoids and let `J𝒴` be the
topology inherited from `(𝒞, J)`. The uniqueness half of the `Isom` sheaf condition for
`q` says that an endomorphism of an object of `𝒴` lying over an identity of `𝒞` is
determined by its restrictions along a `J𝒴`-covering family; specialised to the constant
gluing family it says that such an endomorphism restricting to each member of the family
is the identity.

That is what identifies the `𝒴`-base of a morphism glued over `𝒞` as an identity, and so
what upgrades a glued fibre morphism for `p` to a fibre morphism for `F` in
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/IsomSheaf.lean`.

## Main results

* `CategoryTheory.Functor.fibre_base_id_of_cover`: separatedness of the `Isom` sheaf
  of `q`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- A strongly cartesian arrow `g` of `𝒴` over `q.map g` gives a restriction of its target. -/
private def restrictionOfCart (q : 𝒴 ⥤ 𝒞) {V U : 𝒴} (g : V ⟶ U) (b : q.obj V ⟶ q.obj U)
    (hb : b = q.map g) (hg : q.IsStronglyCartesian (q.map g) g) : Restriction q b U rfl where
  pt := V
  hpt := rfl
  hom := g
  isHomLift := by subst hb; simp
  isCart := by subst hb; simpa using hg

/-- The identity of an object over `U` is a fibre morphism. -/
private theorem fibreHom_id (q : 𝒴 ⥤ 𝒞) {a : 𝒴} {U : 𝒞} (ha : q.obj a = U) :
    FibreHom q a a ha ha (𝟙 a) := by
  unfold FibreHom
  simp

/-- Separatedness of the `Isom` sheaf of a stack in groupoids `q`. An endomorphism
`b : U ⟶ U` of `𝒴` lying over the identity of `q.obj U` whose precomposition with every
member of a `J𝒴`-covering family `{ f i }` is that member, is the identity. This is the
uniqueness half of the `Isom` sheaf condition for `q`, applied to the `J`-covering
family `{ q.map (f i) }` of `𝒞` with `x = y = U` and the constant gluing family. -/
theorem fibre_base_id_of_cover
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (q : 𝒴 ⥤ 𝒞) (hq : IsStackInGroupoids.{w} q J)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} {I : Type w} (V : I → 𝒴) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    -- the 𝒴-overlaps `V i ×_U V j`, which exist for covering families of the
    -- inherited topology (Stacks, Categories Lemma 4.35.15), together with the fact
    -- that their 𝒞-image is again a pullback (`IsFiberedInGroupoids.isPullback_map`):
    (Vij : I → I → 𝒴)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij' : ∀ i j, IsPullback (q.map (pr₁ i j)) (q.map (pr₂ i j))
      (q.map (f i)) (q.map (f j)))
    (b : U ⟶ U) (hb : q.IsHomLift (𝟙 (q.obj U)) b)
    (hbf : ∀ i, f i ≫ b = f i) : b = 𝟙 U := by
  -- Apply the uniqueness half of the `Isom` sheaf condition of `q` to the 𝒞-cover
  -- `{q.map (f i)}`, with `x = y = U`, restrictions `xr i = (V i, f i)`, overlap
  -- restrictions `xrij i j = (Vij i j, pr₁ i j ≫ f i)` and gluing family `𝟙 (V i)`.
  -- Both `b` and `𝟙 U` solve the gluing problem, so the `∃!` forces `b = 𝟙 U`.
  have hf_cart : ∀ i, q.IsStronglyCartesian (q.map (f i)) (f i) :=
    fun i => hq.isFiberedInGroupoids.isStronglyCartesian (f i)
  have hcov : Sieve.ofArrows (fun i => q.obj (V i)) (fun i => q.map (f i)) ∈ J (q.obj U) :=
    (hJ𝒴 V f hf_cart).mp hf
  -- The restrictions `xr i = (V i, f i)` and the overlap restrictions
  -- `xrij i j = (Vij i j, pr₁ i j ≫ f i)` of `U`; the latter is strongly cartesian as a
  -- composite of strongly cartesian arrows.
  let xr : ∀ i, Restriction q (q.map (f i)) U rfl := fun i =>
    restrictionOfCart q (f i) _ rfl (hf_cart i)
  let xrij : ∀ i j, Restriction q (q.map (pr₁ i j) ≫ q.map (f i)) U rfl := fun i j =>
    haveI := hf_cart i
    haveI := hq.isFiberedInGroupoids.isStronglyCartesian (pr₁ i j)
    restrictionOfCart q (pr₁ i j ≫ f i) _ (q.map_comp _ _).symm
      (by rw [q.map_comp]; exact .comp q)
  -- The gluing family is the constant family `𝟙 (V i)`; the witnesses on overlaps are
  -- identities, as the restriction of an identity is an identity.
  have hsheaf := hq.isom_isSheaf U U rfl rfl
    (fun i => q.obj (V i)) (fun i => q.map (f i)) hcov
    (fun i j => q.obj (Vij i j)) (fun i j => q.map (pr₁ i j)) (fun i j => q.map (pr₂ i j))
    hVij' xr xr xrij xrij
  obtain ⟨g, -, hg_uniq⟩ := hsheaf (fun i => 𝟙 (xr i).pt) (fun i => fibreHom_id q _)
    (fun i => inferInstance)
    (fun i j => ⟨𝟙 _, fibreHom_id q _, by simp [IsRestrictionOf], by simp [IsRestrictionOf]⟩)
  -- `b` and `𝟙 U` are both solutions, so both equal `g`.
  have hb_sol : FibreHom q U U rfl rfl b ∧ IsIso b ∧
      ∀ i, (xr i).hom ≫ b = 𝟙 (xr i).pt ≫ (xr i).hom :=
    ⟨by simpa [FibreHom] using hb, isIso_of_isHomLift_id q hq.isFiberedInGroupoids b hb,
      fun i => by simp [xr, restrictionOfCart, hbf]⟩
  have hid_sol : FibreHom q U U rfl rfl (𝟙 U) ∧ IsIso (𝟙 U) ∧
      ∀ i, (xr i).hom ≫ 𝟙 U = 𝟙 (xr i).pt ≫ (xr i).hom :=
    ⟨fibreHom_id q rfl, inferInstance, fun i => by simp [xr, restrictionOfCart]⟩
  rw [hg_uniq b hb_sol, ← hg_uniq (𝟙 U) hid_sol]

end CategoryTheory.Functor
