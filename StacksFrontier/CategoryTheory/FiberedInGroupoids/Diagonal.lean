module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# Fully faithful 1-morphisms and the diagonal (Stacks 04Z7)

Fix a base category `𝒞`. Let `p𝒮 : 𝒮 ⥤ 𝒞` and `p𝒮' : 𝒮' ⥤ 𝒞` be categories fibred in groupoids
and let `G : 𝒮 ⥤ 𝒮'` be a 1-morphism over `𝒞`. Stacks 04Z7 (Lemma 4.35.9) says that `G` is fully
faithful if and only if the diagonal

`Δ_G : 𝒮 ⟶ 𝒮 ×_{G, 𝒮', G} 𝒮`

is an equivalence, the 2-fibre product being the one of Stacks 0040
(`CategoryTheory.TwoFibreProductOver`).

Three of the four implications are formal and need no hypothesis on `p𝒮`, `p𝒮'` at all, because a
morphism `Δ_G x ⟶ Δ_G y` of the 2-fibre product is exactly a *pair* `(a, b)` of morphisms
`x ⟶ y` with `G a = G b`:

* `Δ_G` is always faithful (`faithful_diagonal`);
* `Δ_G` is full precisely when `G` is faithful (`full_diagonal`, `faithful_of_full_diagonal`);
* if `G` is fully faithful then `Δ_G` is essentially surjective (`essSurj_diagonal`): the
  comparison isomorphism `φ : G x ≅ G y` of an object of the 2-fibre product is `G β` for a
  unique `β`, which is invertible because a fully faithful functor reflects isomorphisms.

The one implication that uses the fibred-in-groupoids hypotheses is that essential surjectivity of
`Δ_G` forces `G` to be *full* (`full_of_essSurj_diagonal`): an arbitrary `u : G x ⟶ G x'` need not
be vertical, and one first replaces it by a vertical isomorphism. Lifting the base morphism of `u`
along `p𝒮` gives `ψ : x₀ ⟶ x'`; both `u` and `G ψ` are then strongly cartesian in `𝒮'` over that
base morphism, so they differ by a unique vertical isomorphism `α : G x ≅ G x₀`
(`Functor.IsStronglyCartesian.domainIsoOfBaseIso`) with `α ≫ G ψ = u`. Essential surjectivity
applied to `(x, x₀, α)` writes `α` as `G β`, and then `u = G (β ≫ ψ)`.

## Main results

* `CategoryTheory.TwoFibreProductOver.diagonal`: the diagonal 1-morphism `Δ_G`.
* `CategoryTheory.TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal`:
  **Stacks 04Z7**.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]
variable {𝒮' : Type u₃} [Category.{v₃} 𝒮']
variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

/-- The diagonal 1-morphism `Δ_G : 𝒮 ⥤ 𝒮 ×_{G, 𝒮', G} 𝒮` of a functor `G : 𝒮 ⥤ 𝒮'` strictly over
`𝒞`: it sends `x` to the triple `(x, x, id_{G x})`, whose comparison isomorphism is vertical
because it is an identity, and a morphism `f` to the pair `(f, f)`. -/
def diagonal (hG : G ⋙ p𝒮' = p𝒮) : 𝒮 ⥤ TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G where
  obj x :=
    { base := p𝒮.obj x
      x := x
      y := x
      hx := rfl
      hy := rfl
      iso := Iso.refl (G.obj x)
      vertical := IsHomLift.id (Functor.congr_obj hG x) }
  map f :=
    { hbase := p𝒮.map f
      a := f
      b := f
      ha := inferInstance
      hb := inferInstance
      w := by simp }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

-- The two components of `Δ_G x` are the same object `x` of `𝒮`, and both the `≫` below and the
-- `IsIso` instances for the components of `homDiagonal` need that at instance transparency, which
-- a plain `def` does not provide.
attribute [local instance_reducible] diagonal

@[simp] lemma diagonal_obj_x (hG : G ⋙ p𝒮' = p𝒮) (x : 𝒮) : ((diagonal hG).obj x).x = x := rfl

@[simp] lemma diagonal_obj_y (hG : G ⋙ p𝒮' = p𝒮) (x : 𝒮) : ((diagonal hG).obj x).y = x := rfl

@[simp] lemma diagonal_obj_iso (hG : G ⋙ p𝒮' = p𝒮) (x : 𝒮) :
    ((diagonal hG).obj x).iso = Iso.refl (G.obj x) := rfl

@[simp] lemma diagonal_map_a (hG : G ⋙ p𝒮' = p𝒮) {x y : 𝒮} (f : x ⟶ y) :
    ((diagonal hG).map f).a = f := rfl

@[simp] lemma diagonal_map_b (hG : G ⋙ p𝒮' = p𝒮) {x y : 𝒮} (f : x ⟶ y) :
    ((diagonal hG).map f).b = f := rfl

/-- The two components of a morphism `Δ_G x ⟶ Δ_G y` have the same image under `G`: this is the
comparison square of the 2-fibre product, both comparison isomorphisms being identities. -/
lemma map_eq_of_hom_diagonal (hG : G ⋙ p𝒮' = p𝒮) {x y : 𝒮}
    (Φ : (diagonal hG).obj x ⟶ (diagonal hG).obj y) : G.map Φ.a = G.map Φ.b := by
  simpa using Φ.w

/-- A morphism `β` of `𝒮` whose image under `G` is the (vertical) comparison isomorphism of an
object `P` of the 2-fibre product lies over the canonical `eqToHom` identifying the two base
identifications of `P`. -/
lemma isHomLift_of_map_eq_iso (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
    (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) : p𝒮.IsHomLift (eqToHom P.hx) β := by
  have hvert : p𝒮'.IsHomLift (𝟙 P.base) (G.map β) := by rw [hβ]; exact P.vertical
  have hmap : p𝒮'.IsHomLift (eqToHom P.hx) (G.map β) := by
    refine IsHomLift.of_fac' p𝒮' (eqToHom P.hx) (G.map β) (Functor.congr_obj hG P.x)
      (IsHomLift.codomain_eq p𝒮' (𝟙 P.base) (G.map β)) ?_
    rw [IsHomLift.fac' p𝒮' (𝟙 P.base) (G.map β)]
    simp
  subst hG
  exact IsHomLift.of_fac' _ (eqToHom P.hx) β
    (IsHomLift.domain_eq p𝒮' (eqToHom P.hx) (G.map β))
    (IsHomLift.codomain_eq p𝒮' (eqToHom P.hx) (G.map β))
    (IsHomLift.fac' p𝒮' (eqToHom P.hx) (G.map β))

/-- The comparison morphism `Δ_G P.x ⟶ P` determined by a morphism `β : P.x ⟶ P.y` whose image
under `G` is the comparison isomorphism of `P`. Its first component is an identity and its second
is `β`. -/
def homDiagonal (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G) (β : P.x ⟶ P.y)
    (hβ : G.map β = P.iso.hom) : (diagonal hG).obj P.x ⟶ P where
  hbase := eqToHom P.hx
  a := 𝟙 P.x
  b := β
  ha := IsHomLift.of_fac' p𝒮 (eqToHom P.hx) (𝟙 P.x) rfl P.hx (by simp)
  hb := isHomLift_of_map_eq_iso hG P β hβ
  w := by simpa using hβ.symm

@[simp] lemma homDiagonal_hbase (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
    (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) :
    (homDiagonal hG P β hβ).hbase = eqToHom P.hx := rfl

@[simp] lemma homDiagonal_a (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
    (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) : (homDiagonal hG P β hβ).a = 𝟙 P.x := rfl

@[simp] lemma homDiagonal_b (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
    (β : P.x ⟶ P.y) (hβ : G.map β = P.iso.hom) : (homDiagonal hG P β hβ).b = β := rfl

/-- An object of the 2-fibre product whose comparison isomorphism is `G β` for an *invertible* `β`
is in the essential image of the diagonal: `homDiagonal` has invertible data, hence is invertible
by `isIso_of_components`. -/
lemma essImage_diagonal (hG : G ⋙ p𝒮' = p𝒮) (P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
    (β : P.x ⟶ P.y) [IsIso β] (hβ : G.map β = P.iso.hom) : (diagonal hG).essImage P := by
  have : IsIso (homDiagonal hG P β hβ).hbase := by rw [homDiagonal_hbase]; infer_instance
  have : IsIso (homDiagonal hG P β hβ).a := by rw [homDiagonal_a]; infer_instance
  have : IsIso (homDiagonal hG P β hβ).b := by rw [homDiagonal_b]; infer_instance
  have := isIso_of_components (homDiagonal hG P β hβ)
  exact ⟨P.x, ⟨asIso (homDiagonal hG P β hβ)⟩⟩

/-- Conversely, an isomorphism `Δ_G z ≅ P` writes the comparison isomorphism of `P` as the image
under `G` of a morphism `P.x ⟶ P.y`, namely `inv a ≫ b` for the two components `a`, `b` of the
isomorphism. -/
lemma exists_map_eq_iso_of_iso_diagonal (hG : G ⋙ p𝒮' = p𝒮)
    {P : TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G} {z : 𝒮} (ι : (diagonal hG).obj z ≅ P) :
    ∃ β : P.x ⟶ P.y, G.map β = P.iso.hom := by
  have : IsIso ι.hom.a := by
    have : IsIso ((fst p𝒮 p𝒮 p𝒮' G G).map ι.hom) := inferInstance
    exact this
  have hw : G.map ι.hom.a ≫ P.iso.hom = G.map ι.hom.b := by simpa using ι.hom.w
  exact ⟨inv ι.hom.a ≫ ι.hom.b, by
    rw [G.map_comp, G.map_inv, ← hw, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]⟩

/-- The diagonal is faithful, with no hypothesis: it is already injective on the first component.
-/
theorem faithful_diagonal (hG : G ⋙ p𝒮' = p𝒮) : (diagonal hG).Faithful where
  map_injective h := by simpa using congrArg Hom.a h

/-- If `G` is faithful then the diagonal is full: a morphism `Δ_G x ⟶ Δ_G y` is a pair `(a, b)`
with `G a = G b`, hence with `a = b`, hence in the image of `Δ_G`. -/
theorem full_diagonal (hG : G ⋙ p𝒮' = p𝒮) [G.Faithful] : (diagonal hG).Full where
  map_surjective Φ :=
    ⟨Φ.a, Hom.ext' rfl (G.map_injective (map_eq_of_hom_diagonal hG Φ))⟩

/-- Conversely, if the diagonal is full then `G` is faithful: two morphisms `f, g : x ⟶ y` with
`G f = G g` assemble into a morphism `Δ_G x ⟶ Δ_G y`, and any preimage of it under `Δ_G` equals
both `f` and `g`. -/
theorem faithful_of_full_diagonal (hG : G ⋙ p𝒮' = p𝒮) (h : (diagonal hG).Full) : G.Faithful where
  map_injective {x y} f g hfg := by
    have hbase : p𝒮.map g = p𝒮.map f := by
      have h₁ := Functor.congr_hom hG f
      have h₂ := Functor.congr_hom hG g
      simp only [Functor.comp_map, hfg] at h₁ h₂
      have h₃ := h₁.symm.trans h₂
      simp only [cancel_epi, cancel_mono] at h₃
      exact h₃.symm
    have hb : p𝒮.IsHomLift (p𝒮.map f) g := by
      rw [← hbase]; exact IsHomLift.map (p := p𝒮) g
    obtain ⟨h₀, hh₀⟩ := h.map_surjective
      ({ hbase := p𝒮.map f, a := f, b := g, ha := IsHomLift.map (p := p𝒮) f, hb := hb,
          w := by simpa using hfg } : (diagonal hG).obj x ⟶ (diagonal hG).obj y)
    have hfa : h₀ = f := by simpa using congrArg Hom.a hh₀
    have hgb : h₀ = g := by simpa using congrArg Hom.b hh₀
    rw [← hfa, hgb]

/-- If `G` is fully faithful then the diagonal is essentially surjective: for an object
`P = (x, y, φ)` of the 2-fibre product, fullness writes `φ = G β`, faithfulness makes `β`
invertible, and `essImage_diagonal` concludes. -/
theorem essSurj_diagonal (hG : G ⋙ p𝒮' = p𝒮) [G.Full] [G.Faithful] :
    (diagonal hG).EssSurj where
  mem_essImage P := by
    obtain ⟨β, hβ⟩ := Functor.Full.map_surjective (F := G) P.iso.hom
    have : IsIso (G.map β) := by rw [hβ]; infer_instance
    have : IsIso β := isIso_of_fully_faithful G β
    exact essImage_diagonal hG P β hβ

/-- Essential surjectivity of the diagonal writes every *vertical* isomorphism `G x ≅ G y` between
images of objects of `𝒮` lying over a common `U` as `G β`. -/
lemma exists_map_eq_of_essSurj_diagonal (hG : G ⋙ p𝒮' = p𝒮) (hΔ : (diagonal hG).EssSurj)
    {U : 𝒞} {x y : 𝒮} (hx : p𝒮.obj x = U) (hy : p𝒮.obj y = U) (φ : G.obj x ≅ G.obj y)
    (hφ : p𝒮'.IsHomLift (𝟙 U) φ.hom) : ∃ β : x ⟶ y, G.map β = φ.hom := by
  obtain ⟨z, ⟨ι⟩⟩ := hΔ.mem_essImage
    ({ base := U, x := x, y := y, hx := hx, hy := hy, iso := φ, vertical := hφ } :
      TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G)
  exact exists_map_eq_iso_of_iso_diagonal hG ι

/-- **The one substantive implication.** If `p𝒮` and `p𝒮'` are fibred in groupoids and the
diagonal is essentially surjective, then `G` is full.

An arbitrary `u : G x ⟶ G x'` need not be vertical. Lift its base morphism along `p𝒮` to
`ψ : x₀ ⟶ x'`; in a category fibred in groupoids both `u` and `G ψ` are strongly cartesian over
that base morphism, so they differ by a vertical isomorphism `α : G x ≅ G x₀` with `α ≫ G ψ = u`.
Essential surjectivity writes `α` as `G β`, and then `u = G (β ≫ ψ)`. -/
theorem full_of_essSurj_diagonal (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (h𝒮' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮) (hΔ : (diagonal hG).EssSurj) :
    G.Full where
  map_surjective {x x'} u := by
    have hx : p𝒮'.obj (G.obj x) = p𝒮.obj x := Functor.congr_obj hG x
    have hx' : p𝒮'.obj (G.obj x') = p𝒮.obj x' := Functor.congr_obj hG x'
    set f : p𝒮.obj x ⟶ p𝒮.obj x' := eqToHom hx.symm ≫ p𝒮'.map u ≫ eqToHom hx' with hf
    have hu : p𝒮'.IsHomLift f u := IsHomLift.of_fac' p𝒮' f u hx hx' (by simp [hf])
    obtain ⟨x₀, ψ, hψ⟩ := h𝒮.exists_lift f x' rfl
    have := hψ
    have := Functor.isHomLift_map_of_comp_eq hG f ψ
    have := h𝒮'.isStronglyCartesian_homLift f (G.map ψ)
    have := h𝒮'.isStronglyCartesian_homLift f u
    have hrefl : f = (Iso.refl (p𝒮.obj x)).hom ≫ f := by simp
    set α : G.obj x ≅ G.obj x₀ :=
      Functor.IsStronglyCartesian.domainIsoOfBaseIso p𝒮' hrefl (G.map ψ) u with hα
    have hαfac : α.hom ≫ G.map ψ = u := by
      rw [hα, Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
      exact Functor.IsStronglyCartesian.fac p𝒮' f (G.map ψ) hrefl u
    have hαvert : p𝒮'.IsHomLift (𝟙 (p𝒮.obj x)) α.hom := by
      have := Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p𝒮' hrefl (G.map ψ) u
      simpa [hα] using this
    obtain ⟨β, hβ⟩ := exists_map_eq_of_essSurj_diagonal hG hΔ (rfl : p𝒮.obj x = p𝒮.obj x)
      (IsHomLift.domain_eq p𝒮 f ψ) α hαvert
    exact ⟨β ≫ ψ, by rw [G.map_comp, hβ, hαfac]⟩

/-- **Stacks 04Z7.** Let `p𝒮 : 𝒮 ⥤ 𝒞` and `p𝒮' : 𝒮' ⥤ 𝒞` be categories fibred in groupoids and
let `G : 𝒮 ⥤ 𝒮'` be a 1-morphism over `𝒞`. Then `G` is fully faithful if and only if the diagonal
`Δ_G : 𝒮 ⥤ 𝒮 ×_{G, 𝒮', G} 𝒮` is an equivalence. -/
@[stacks 04Z7]
theorem full_and_faithful_iff_isEquivalence_diagonal (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (h𝒮' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮) :
    (G.Full ∧ G.Faithful) ↔ (diagonal hG).IsEquivalence := by
  constructor
  · rintro ⟨hfull, hfaithful⟩
    exact { faithful := faithful_diagonal hG
            full := full_diagonal hG
            essSurj := essSurj_diagonal hG }
  · intro hΔ
    have hfaithful : G.Faithful := faithful_of_full_diagonal hG hΔ.full
    exact ⟨full_of_essSurj_diagonal h𝒮 h𝒮' hG hΔ.essSurj, hfaithful⟩

end CategoryTheory.TwoFibreProductOver
