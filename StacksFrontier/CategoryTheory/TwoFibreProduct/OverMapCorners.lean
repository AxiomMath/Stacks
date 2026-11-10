module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Changing all three corners of a 2-fibre product over a base

Fix a base category `𝒞` and two cospans of categories over `𝒞`,
`F : 𝒳 ⥤ 𝒮 ⟵ 𝒴 : G` and `F' : 𝒳' ⥤ 𝒮' ⟵ 𝒴' : G'`, with their 2-fibre products over `𝒞`
(`CategoryTheory.TwoFibreProductOver`, Stacks 0040). Three functors `a : 𝒳 ⥤ 𝒳'`,
`b : 𝒴 ⥤ 𝒴'`, `c : 𝒮 ⥤ 𝒮'` strictly over `𝒞`, compatible with the legs up to natural
isomorphisms `α : F ⋙ c ≅ a ⋙ F'` and `β : G ⋙ c ≅ b ⋙ G'` whose components are vertical,
induce a functor `𝒳 ×_𝒮 𝒴 ⥤ 𝒳' ×_𝒮' 𝒴'` over `𝒞`: an object `(U, x, y, φ)` goes to
`(U, a x, b y, β ∘ c φ ∘ α⁻¹)`.

When the three functors are equivalences over `𝒞` this functor is an equivalence of
categories: the 2-fibre product over `𝒞` is invariant under replacing the three corners of the
cospan by equivalent ones, compatibly with the two legs up to vertical 2-isomorphisms. The
files `StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality` and
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison` change one corner at a time and
with the legs matching on the nose or keeping one factor fixed; here all three corners change
at once and the legs match only up to 2-isomorphism, which is the shape in which a comparison
of two descriptions of the same 2-fibre product arrives.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapCorners`: the induced functor.

## Main results

* `CategoryTheory.TwoFibreProductOver.mapCorners_comp_structureFunctor`: it is over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.faithful_mapCorners`,
  `CategoryTheory.TwoFibreProductOver.full_mapCorners` and
  `CategoryTheory.TwoFibreProductOver.essSurj_mapCorners`: it is faithful, full and
  essentially surjective as soon as `a`, `b`, `c` are, essential surjectivity of `a` and `b`
  being asked through vertical isomorphisms.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_mapCorners`: **it is an equivalence when
  the three functors are the forward 1-morphisms of equivalences over `𝒞`.**
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

open StacksRepresentableCFG

universe vC v₁ v₂ v₃ v₄ v₅ v₆ uC u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒞 : Type uC} [Category.{vC} 𝒞]
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒳' : Type u₄} [Category.{v₄} 𝒳']
  {𝒴' : Type u₅} [Category.{v₅} 𝒴'] {𝒮' : Type u₆} [Category.{v₆} 𝒮']
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞}
  {p𝒮' : 𝒮' ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮} {F' : 𝒳' ⥤ 𝒮'} {G' : 𝒴' ⥤ 𝒮'}

/-- A morphism whose image under a functor over `𝒞` lies over `f` itself lies over `f`. -/
private theorem isHomLift_of_isHomLift_map {𝒵 𝒵' : Type*} [Category 𝒵] [Category 𝒵']
    {q : 𝒵 ⥤ 𝒞} {q' : 𝒵' ⥤ 𝒞} {k : 𝒵 ⥤ 𝒵'} (hk : k ⋙ q' = q) {R T : 𝒞} (f : R ⟶ T)
    {u v : 𝒵} (φ : u ⟶ v) (h : q'.IsHomLift f (k.map φ)) : q.IsHomLift f φ := by
  subst hk
  subst_hom_lift q' f (k.map φ)
  exact .map φ

/-- The inverse of an isomorphism lying over an identity lies over that identity. -/
private theorem isHomLift_id_inv_of_eq {𝒵 : Type*} [Category 𝒵] {q : 𝒵 ⥤ 𝒞} {X Y : 𝒵} {U : 𝒞}
    (e : X ≅ Y) (hU : q.obj X = U) (h : q.IsHomLift (𝟙 (q.obj X)) e.hom) :
    q.IsHomLift (𝟙 U) e.inv := by
  subst hU
  simpa using IsHomLift.lift_id_inv_isIso q (q.obj X) e.hom

section MapCorners

variable {a : 𝒳 ⥤ 𝒳'} {b : 𝒴 ⥤ 𝒴'} {c : 𝒮 ⥤ 𝒮'}
  (ha : a ⋙ p𝒳' = p𝒳) (hb : b ⋙ p𝒴' = p𝒴) (hc : c ⋙ p𝒮' = p𝒮)
  (α : F ⋙ c ≅ a ⋙ F') (β : G ⋙ c ≅ b ⋙ G')
  (hα : ∀ x, p𝒮'.IsHomLift (𝟙 (p𝒮'.obj (c.obj (F.obj x)))) (α.hom.app x))
  (hβ : ∀ y, p𝒮'.IsHomLift (𝟙 (p𝒮'.obj (c.obj (G.obj y)))) (β.hom.app y))

include hc hα hβ in
/-- The comparison isomorphism of the image of an object is vertical. -/
theorem mapCorners_vertical (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    p𝒮'.IsHomLift (𝟙 P.base) (α.inv.app P.x ≫ c.map P.iso.hom ≫ β.hom.app P.y) := by
  have hP := P.vertical
  have hF : p𝒮'.obj (c.obj (F.obj P.x)) = P.base :=
    (Functor.congr_obj hc _).trans (IsHomLift.domain_eq p𝒮 (𝟙 P.base) P.iso.hom)
  have hG : p𝒮'.obj (c.obj (G.obj P.y)) = P.base :=
    (Functor.congr_obj hc _).trans (IsHomLift.codomain_eq p𝒮 (𝟙 P.base) P.iso.hom)
  have h₁ : p𝒮'.IsHomLift (𝟙 P.base) (α.inv.app P.x) :=
    isHomLift_id_inv_of_eq (α.app P.x) hF (hα P.x)
  have h₂ : p𝒮'.IsHomLift (𝟙 P.base) (c.map P.iso.hom) :=
    Functor.isHomLift_map_of_comp_eq hc (𝟙 P.base) P.iso.hom
  have h₃ : p𝒮'.IsHomLift (𝟙 P.base) (β.hom.app P.y) := by
    have h := hβ P.y
    rw [hG] at h
    exact h
  infer_instance

/-- The image of an object of `𝒳 ×_𝒮 𝒴` in `𝒳' ×_𝒮' 𝒴'`. -/
def mapCornersObj (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    TwoFibreProductOver p𝒳' p𝒴' p𝒮' F' G' where
  base := P.base
  x := a.obj P.x
  y := b.obj P.y
  hx := (Functor.congr_obj ha P.x).trans P.hx
  hy := (Functor.congr_obj hb P.y).trans P.hy
  iso := (α.app P.x).symm ≪≫ c.mapIso P.iso ≪≫ β.app P.y
  vertical := mapCorners_vertical hc α β hα hβ P

/-- The image of a morphism of `𝒳 ×_𝒮 𝒴` in `𝒳' ×_𝒮' 𝒴'`. -/
def mapCornersMap {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) :
    mapCornersObj ha hb hc α β hα hβ P ⟶ mapCornersObj ha hb hc α β hα hβ Q where
  hbase := f.hbase
  a := a.map f.a
  b := b.map f.b
  ha := by
    have := f.ha
    exact Functor.isHomLift_map_of_comp_eq ha f.hbase f.a
  hb := by
    have := f.hb
    exact Functor.isHomLift_map_of_comp_eq hb f.hbase f.b
  w := by
    change F'.map (a.map f.a) ≫ α.inv.app Q.x ≫ c.map Q.iso.hom ≫ β.hom.app Q.y =
      (α.inv.app P.x ≫ c.map P.iso.hom ≫ β.hom.app P.y) ≫ G'.map (b.map f.b)
    have h₁ : F'.map (a.map f.a) ≫ α.inv.app Q.x = α.inv.app P.x ≫ c.map (F.map f.a) :=
      α.inv.naturality f.a
    have h₂ : c.map (G.map f.b) ≫ β.hom.app Q.y = β.hom.app P.y ≫ G'.map (b.map f.b) :=
      β.hom.naturality f.b
    have h₃ : c.map (F.map f.a) ≫ c.map Q.iso.hom = c.map P.iso.hom ≫ c.map (G.map f.b) := by
      rw [← c.map_comp, ← c.map_comp, f.w]
    rw [reassoc_of% h₁, reassoc_of% h₃, h₂]
    simp only [Category.assoc]

/-- **The functor `𝒳 ×_𝒮 𝒴 ⥤ 𝒳' ×_𝒮' 𝒴'` induced by changing the three corners of the
cospan.** An object `(U, x, y, φ)` goes to `(U, a x, b y, β ∘ c φ ∘ α⁻¹)` and a morphism
`(f, g)` to `(a f, b g)`. -/
def mapCorners :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ TwoFibreProductOver p𝒳' p𝒴' p𝒮' F' G' where
  obj := mapCornersObj ha hb hc α β hα hβ
  map := mapCornersMap ha hb hc α β hα hβ
  map_id P := Hom.ext' (a.map_id P.x) (b.map_id P.y)
  map_comp f g := Hom.ext' (a.map_comp f.a g.a) (b.map_comp f.b g.b)

/-- The `𝒳'`-component of the image of a morphism. -/
@[simp] theorem mapCorners_map_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) :
    ((mapCorners ha hb hc α β hα hβ).map f).a = a.map f.a := rfl

/-- The `𝒴'`-component of the image of a morphism. -/
@[simp] theorem mapCorners_map_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) :
    ((mapCorners ha hb hc α β hα hβ).map f).b = b.map f.b := rfl

/-- The induced functor is strictly over `𝒞`. -/
theorem mapCorners_comp_structureFunctor :
    mapCorners ha hb hc α β hα hβ ⋙ structureFunctor p𝒳' p𝒴' p𝒮' F' G' =
      structureFunctor p𝒳 p𝒴 p𝒮 F G :=
  rfl

/-- The induced functor is faithful when `a` and `b` are. -/
theorem faithful_mapCorners [a.Faithful] [b.Faithful] :
    (mapCorners ha hb hc α β hα hβ).Faithful where
  map_injective {_ _} {_ _} h :=
    Hom.ext' (a.map_injective (congrArg Hom.a h)) (b.map_injective (congrArg Hom.b h))

/-- The induced functor is full when `a`, `b` are full and `c` is faithful. -/
theorem full_mapCorners [a.Full] [b.Full] [c.Faithful] :
    (mapCorners ha hb hc α β hα hβ).Full where
  map_surjective {P Q} g := by
    let ga : a.obj P.x ⟶ a.obj Q.x := g.a
    let gb : b.obj P.y ⟶ b.obj Q.y := g.b
    have hga : p𝒳'.IsHomLift g.hbase ga := g.ha
    have hgb : p𝒴'.IsHomLift g.hbase gb := g.hb
    have hla : p𝒳.IsHomLift g.hbase (a.preimage ga) :=
      isHomLift_of_isHomLift_map ha g.hbase _ (by rw [a.map_preimage]; exact hga)
    have hlb : p𝒴.IsHomLift g.hbase (b.preimage gb) :=
      isHomLift_of_isHomLift_map hb g.hbase _ (by rw [b.map_preimage]; exact hgb)
    refine ⟨⟨g.hbase, a.preimage ga, b.preimage gb, hla, hlb, ?_⟩, ?_⟩
    · apply c.map_injective
      have hw : F'.map ga ≫ α.inv.app Q.x ≫ c.map Q.iso.hom ≫ β.hom.app Q.y =
          (α.inv.app P.x ≫ c.map P.iso.hom ≫ β.hom.app P.y) ≫ G'.map gb := g.w
      have h₁ : c.map (F.map (a.preimage ga)) =
          α.hom.app P.x ≫ F'.map ga ≫ α.inv.app Q.x := by
        have h : c.map (F.map (a.preimage ga)) ≫ α.hom.app Q.x =
            α.hom.app P.x ≫ F'.map (a.map (a.preimage ga)) := α.hom.naturality (a.preimage ga)
        rw [a.map_preimage] at h
        rw [← reassoc_of% h]
        simp
      have h₂ : c.map (G.map (b.preimage gb)) =
          β.hom.app P.y ≫ G'.map gb ≫ β.inv.app Q.y := by
        have h : c.map (G.map (b.preimage gb)) ≫ β.hom.app Q.y =
            β.hom.app P.y ≫ G'.map (b.map (b.preimage gb)) := β.hom.naturality (b.preimage gb)
        rw [b.map_preimage] at h
        rw [← reassoc_of% h]
        simp
      rw [c.map_comp, c.map_comp, h₁, h₂]
      have hw' := congrArg (fun t => α.hom.app P.x ≫ t ≫ β.inv.app Q.y) hw
      simpa using hw'
    · exact Hom.ext' (a.map_preimage ga) (b.map_preimage gb)

/-- The induced functor is essentially surjective when `c` is full and faithful, `F'` and `G'`
are over `𝒞`, and every object of `𝒳'` and of `𝒴'` receives a vertical isomorphism from an
object in the image of `a`, respectively `b`. -/
theorem essSurj_mapCorners [c.Full] [c.Faithful] (hF' : F' ⋙ p𝒮' = p𝒳')
    (hG' : G' ⋙ p𝒮' = p𝒴')
    (hea : ∀ x' : 𝒳', ∃ (x : 𝒳) (i : a.obj x ≅ x'), p𝒳'.IsHomLift (𝟙 (p𝒳'.obj x')) i.hom)
    (heb : ∀ y' : 𝒴', ∃ (y : 𝒴) (j : b.obj y ≅ y'), p𝒴'.IsHomLift (𝟙 (p𝒴'.obj y')) j.hom) :
    (mapCorners ha hb hc α β hα hβ).EssSurj where
  mem_essImage Q := by
    obtain ⟨x, i, hi⟩ := hea Q.x
    obtain ⟨y, j, hj⟩ := heb Q.y
    rw [Q.hx] at hi
    rw [Q.hy] at hj
    have hxU : p𝒳.obj x = Q.base :=
      (Functor.congr_obj ha x).symm.trans (IsHomLift.domain_eq p𝒳' (𝟙 Q.base) i.hom)
    have hyU : p𝒴.obj y = Q.base :=
      (Functor.congr_obj hb y).symm.trans (IsHomLift.domain_eq p𝒴' (𝟙 Q.base) j.hom)
    have hαx := hα x
    have hβy := hβ y
    have hRx : p𝒮'.obj (c.obj (F.obj x)) = Q.base :=
      (IsHomLift.codomain_eq p𝒮' (𝟙 (p𝒮'.obj (c.obj (F.obj x)))) (α.hom.app x)).symm.trans
        ((Functor.congr_obj hF' (a.obj x)).trans ((Functor.congr_obj ha x).trans hxU))
    have hRy : p𝒮'.obj (c.obj (G.obj y)) = Q.base :=
      (IsHomLift.codomain_eq p𝒮' (𝟙 (p𝒮'.obj (c.obj (G.obj y)))) (β.hom.app y)).symm.trans
        ((Functor.congr_obj hG' (b.obj y)).trans ((Functor.congr_obj hb y).trans hyU))
    let ψ' : c.obj (F.obj x) ≅ c.obj (G.obj y) :=
      α.app x ≪≫ F'.mapIso i ≪≫ Q.iso ≪≫ G'.mapIso j.symm ≪≫ (β.app y).symm
    have hψ' : p𝒮'.IsHomLift (𝟙 Q.base) ψ'.hom := by
      change p𝒮'.IsHomLift (𝟙 Q.base)
        (α.hom.app x ≫ F'.map i.hom ≫ Q.iso.hom ≫ G'.map j.inv ≫ β.inv.app y)
      have hQ := Q.vertical
      have h₁ : p𝒮'.IsHomLift (𝟙 Q.base) (α.hom.app x) := by
        have h := hα x
        rw [hRx] at h
        exact h
      have h₂ : p𝒮'.IsHomLift (𝟙 Q.base) (F'.map i.hom) :=
        Functor.isHomLift_map_of_comp_eq hF' (𝟙 Q.base) i.hom
      have h₄ : p𝒮'.IsHomLift (𝟙 Q.base) (G'.map j.inv) :=
        Functor.isHomLift_map_of_comp_eq hG' (𝟙 Q.base) j.inv
      have h₅ : p𝒮'.IsHomLift (𝟙 Q.base) (β.inv.app y) :=
        isHomLift_id_inv_of_eq (β.app y) hRy (hβ y)
      infer_instance
    let ψ : F.obj x ≅ G.obj y := c.preimageIso ψ'
    have hcψ : c.map ψ.hom = ψ'.hom := c.map_preimage ψ'.hom
    have hψ : p𝒮.IsHomLift (𝟙 Q.base) ψ.hom :=
      isHomLift_of_isHomLift_map hc (𝟙 Q.base) ψ.hom (by rw [hcψ]; exact hψ')
    let P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
      { base := Q.base, x := x, y := y, hx := hxU, hy := hyU, iso := ψ, vertical := hψ }
    refine ⟨P, ⟨isoMkVertical (U := Q.base) i j hi hj ?_⟩⟩
    change F'.map i.hom ≫ Q.iso.hom =
      (α.inv.app x ≫ c.map ψ.hom ≫ β.hom.app y) ≫ G'.map j.hom
    rw [hcψ]
    simp [ψ']

end MapCorners

/-- **The 2-fibre product over `𝒞` is invariant under equivalences of the three corners.**
Equivalences `ea : 𝒳 ≃ 𝒳'`, `eb : 𝒴 ≃ 𝒴'`, `ec : 𝒮 ≃ 𝒮'` over `𝒞`, compatible with the legs
of the two cospans up to natural isomorphisms with vertical components, induce an equivalence
`𝒳 ×_𝒮 𝒴 ⥤ 𝒳' ×_𝒮' 𝒴'` of the 2-fibre products over `𝒞`. -/
theorem isEquivalence_mapCorners (ea : EquivalenceOver p𝒳 p𝒳') (eb : EquivalenceOver p𝒴 p𝒴')
    (ec : EquivalenceOver p𝒮 p𝒮') (hF' : F' ⋙ p𝒮' = p𝒳') (hG' : G' ⋙ p𝒮' = p𝒴')
    (α : F ⋙ ec.hom.functor ≅ ea.hom.functor ⋙ F')
    (β : G ⋙ ec.hom.functor ≅ eb.hom.functor ⋙ G')
    (hα : ∀ x, p𝒮'.IsHomLift (𝟙 (p𝒮'.obj (ec.hom.functor.obj (F.obj x)))) (α.hom.app x))
    (hβ : ∀ y, p𝒮'.IsHomLift (𝟙 (p𝒮'.obj (ec.hom.functor.obj (G.obj y)))) (β.hom.app y)) :
    (mapCorners ea.hom.w eb.hom.w ec.hom.w α β hα hβ).IsEquivalence := by
  have := ea.isEquivalence_hom_functor
  have := eb.isEquivalence_hom_functor
  have := ec.isEquivalence_hom_functor
  exact
    { faithful := faithful_mapCorners ea.hom.w eb.hom.w ec.hom.w α β hα hβ
      full := full_mapCorners ea.hom.w eb.hom.w ec.hom.w α β hα hβ
      essSurj := essSurj_mapCorners ea.hom.w eb.hom.w ec.hom.w α β hα hβ hF' hG'
        (fun x' => ⟨ea.inv.functor.obj x', ea.counitIso.app x',
          ea.isHomLift_counitIso_hom_app x'⟩)
        (fun y' => ⟨eb.inv.functor.obj y', eb.counitIso.app y',
          eb.isHomLift_counitIso_hom_app y'⟩) }

end CategoryTheory.TwoFibreProductOver

end
