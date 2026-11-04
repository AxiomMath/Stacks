module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# Transporting morphisms of inverse images across a commutative square

For `f₁ : Y ⟶ Z`, `f₂ : Z ⟶ S` and `P = f₁ ≫ f₂`, a morphism `γ : f₁⁻¹ f₂⁻¹ A ⟶ f₁⁻¹ f₂⁻¹ K` of
abelian sheaves on the small étale site of `Y` is read as a morphism `P⁻¹ A ⟶ P⁻¹ K` through the
composition isomorphism of inverse images
(`Stacks.EtaleCohomology.smallEtalePullbackAbConj`). Conjugating twice is conjugating along the
composite (`Stacks.EtaleCohomology.smallEtalePullbackAbConj_assoc`), by the associativity
pentagon of the composition isomorphisms; on a morphism pulled back from `S` it is the inverse
image of that morphism.

For a commutative square `h ≫ a = e ≫ g` this transports a morphism `β : a⁻¹ A ⟶ a⁻¹ K` to a
morphism `e⁻¹ g⁻¹ A ⟶ e⁻¹ g⁻¹ K` (`Stacks.EtaleCohomology.inverseImageSquareTransport`), and the
transport is compatible with pasting a second square
(`Stacks.EtaleCohomology.inverseImageSquareTransport_paste`). This is how the inverse image
`g⁻¹` acts on morphisms that are only defined étale locally on `S`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbConj`.
* `Stacks.EtaleCohomology.inverseImageSquareTransport`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbConj_assoc`.
* `Stacks.EtaleCohomology.inverseImageSquareTransport_paste`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Conj

variable {Y Z S : Scheme.{u}} (f₁ : Y ⟶ Z) (f₂ : Z ⟶ S) (P : Y ⟶ S) (hP : P = f₁ ≫ f₂)

/-- A morphism between iterated inverse images, read as a morphism between inverse images along
the composite. -/
def smallEtalePullbackAbConj {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (γ : (smallEtalePullbackAb f₁).obj ((smallEtalePullbackAb f₂).obj A) ⟶
      (smallEtalePullbackAb f₁).obj ((smallEtalePullbackAb f₂).obj K)) :
    (smallEtalePullbackAb P).obj A ⟶ (smallEtalePullbackAb P).obj K :=
  (smallEtalePullbackAbCompIso' f₁ f₂ P hP).inv.app A ≫ γ ≫
    (smallEtalePullbackAbCompIso' f₁ f₂ P hP).hom.app K

variable {f₁ f₂ P hP} in
/-- Conjugation by the composition isomorphism of inverse images is injective. -/
theorem smallEtalePullbackAbConj_injective {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    {γ γ' : (smallEtalePullbackAb f₁).obj ((smallEtalePullbackAb f₂).obj A) ⟶
      (smallEtalePullbackAb f₁).obj ((smallEtalePullbackAb f₂).obj K)}
    (h : smallEtalePullbackAbConj f₁ f₂ P hP γ = smallEtalePullbackAbConj f₁ f₂ P hP γ') :
    γ = γ' := by
  have := congrArg (fun x => (smallEtalePullbackAbCompIso' f₁ f₂ P hP).hom.app A ≫ x ≫
    (smallEtalePullbackAbCompIso' f₁ f₂ P hP).inv.app K) h
  simpa [smallEtalePullbackAbConj] using this

/-- On a morphism pulled back from `S`, the conjugation is the inverse image along the
composite. -/
theorem smallEtalePullbackAbConj_map {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : A ⟶ K) :
    smallEtalePullbackAbConj f₁ f₂ P hP ((smallEtalePullbackAb f₁).map
        ((smallEtalePullbackAb f₂).map β)) = (smallEtalePullbackAb P).map β := by
  rw [smallEtalePullbackAbConj]
  exact (Iso.inv_comp_eq ((smallEtalePullbackAbCompIso' f₁ f₂ P hP).app A)).2
    ((smallEtalePullbackAbCompIso' f₁ f₂ P hP).hom.naturality β)

/-- **Conjugating twice is conjugating along the composite**, by the associativity pentagon of
the composition isomorphisms of inverse images. -/
theorem smallEtalePullbackAbConj_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁)
    (hq : q = j ≫ i) (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a)
    {A K : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}}
    (γ : (smallEtalePullbackAb i).obj ((smallEtalePullbackAb f).obj A) ⟶
      (smallEtalePullbackAb i).obj ((smallEtalePullbackAb f).obj K)) :
    smallEtalePullbackAbConj j a p hp₂
        ((smallEtalePullbackAb j).map (smallEtalePullbackAbConj i f a ha γ)) =
      smallEtalePullbackAbConj q f p hp₁
        (smallEtalePullbackAbConj j i q hq ((smallEtalePullbackAb j).map γ)) := by
  have hpent : ∀ F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1},
      (smallEtalePullbackAbCompIso' j i q hq).hom.app ((smallEtalePullbackAb f).obj F) ≫
          (smallEtalePullbackAbCompIso' q f p hp₁).hom.app F =
        (smallEtalePullbackAb j).map ((smallEtalePullbackAbCompIso' i f a ha).hom.app F) ≫
          (smallEtalePullbackAbCompIso' j a p hp₂).hom.app F := fun F => by
    have h := congrArg (fun φ => φ.hom.app F)
      (smallEtalePullbackAbCompIso'_assoc f i j a ha q hq p hp₁ hp₂)
    simpa using h
  have hpentinv : ∀ F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1},
      (smallEtalePullbackAbCompIso' q f p hp₁).inv.app F ≫
          (smallEtalePullbackAbCompIso' j i q hq).inv.app ((smallEtalePullbackAb f).obj F) =
        (smallEtalePullbackAbCompIso' j a p hp₂).inv.app F ≫
          (smallEtalePullbackAb j).map ((smallEtalePullbackAbCompIso' i f a ha).inv.app F) := by
    intro F
    have h := congrArg (fun φ => φ.inv.app F)
      (smallEtalePullbackAbCompIso'_assoc f i j a ha q hq p hp₁ hp₂)
    simpa using h
  simp only [smallEtalePullbackAbConj, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hpent K, reassoc_of% hpentinv A]

end Conj

section Square

variable {S S' X Y : Scheme.{u}} (a : S' ⟶ S) (g : X ⟶ S) (h : Y ⟶ S') (e : Y ⟶ X)
  (P : Y ⟶ S) (hPh : P = h ≫ a) (hPe : P = e ≫ g)

/-- **Transport of a morphism of inverse images across a commutative square**: for
`P = h ≫ a = e ≫ g` and `β : a⁻¹ A ⟶ a⁻¹ K`, the morphism `e⁻¹ g⁻¹ A ⟶ e⁻¹ g⁻¹ K` which, read
along `P`, is `h⁻¹ β` read along `P`. -/
def inverseImageSquareTransport {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : (smallEtalePullbackAb a).obj A ⟶ (smallEtalePullbackAb a).obj K) :
    (smallEtalePullbackAb e).obj ((smallEtalePullbackAb g).obj A) ⟶
      (smallEtalePullbackAb e).obj ((smallEtalePullbackAb g).obj K) :=
  (smallEtalePullbackAbCompIso' e g P hPe).hom.app A ≫
    smallEtalePullbackAbConj h a P hPh ((smallEtalePullbackAb h).map β) ≫
      (smallEtalePullbackAbCompIso' e g P hPe).inv.app K

/-- Read along `P`, the transport of `β` is `h⁻¹ β` read along `P`. -/
theorem smallEtalePullbackAbConj_inverseImageSquareTransport
    {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : (smallEtalePullbackAb a).obj A ⟶ (smallEtalePullbackAb a).obj K) :
    smallEtalePullbackAbConj e g P hPe (inverseImageSquareTransport a g h e P hPh hPe β) =
      smallEtalePullbackAbConj h a P hPh ((smallEtalePullbackAb h).map β) := by
  simp [inverseImageSquareTransport, smallEtalePullbackAbConj]

/-- The transport preserves composition of morphisms. -/
theorem inverseImageSquareTransport_comp {A K L : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : (smallEtalePullbackAb a).obj A ⟶ (smallEtalePullbackAb a).obj K)
    (β' : (smallEtalePullbackAb a).obj K ⟶ (smallEtalePullbackAb a).obj L) :
    inverseImageSquareTransport a g h e P hPh hPe (β ≫ β') =
      inverseImageSquareTransport a g h e P hPh hPe β ≫
        inverseImageSquareTransport a g h e P hPh hPe β' := by
  simp [inverseImageSquareTransport, smallEtalePullbackAbConj]

/-- The transport of an identity morphism is the identity. -/
@[simp]
theorem inverseImageSquareTransport_id (A : Sheaf (smallEtaleTopology S) Ab.{u + 1}) :
    inverseImageSquareTransport a g h e P hPh hPe (𝟙 ((smallEtalePullbackAb a).obj A)) = 𝟙 _ := by
  simp [inverseImageSquareTransport, smallEtalePullbackAbConj]

/-- The transport is additive. -/
theorem inverseImageSquareTransport_add {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β β' : (smallEtalePullbackAb a).obj A ⟶ (smallEtalePullbackAb a).obj K) :
    inverseImageSquareTransport a g h e P hPh hPe (β + β') =
      inverseImageSquareTransport a g h e P hPh hPe β +
        inverseImageSquareTransport a g h e P hPh hPe β' := by
  simp [inverseImageSquareTransport, smallEtalePullbackAbConj, CategoryTheory.Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- On a morphism pulled back from `S`, the transport is the inverse image along `e` of its
inverse image along `g`. -/
theorem inverseImageSquareTransport_map {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (u' : A ⟶ K) :
    inverseImageSquareTransport a g h e P hPh hPe ((smallEtalePullbackAb a).map u') =
      (smallEtalePullbackAb e).map ((smallEtalePullbackAb g).map u') := by
  apply smallEtalePullbackAbConj_injective (f₁ := e) (f₂ := g) (P := P) (hP := hPe)
  rw [smallEtalePullbackAbConj_inverseImageSquareTransport, smallEtalePullbackAbConj_map,
    smallEtalePullbackAbConj_map]

/-- **The transport is compatible with pasting a second square** `h' ≫ b = e' ≫ h` (with
`Q = h' ≫ b = e' ≫ h`): transporting the pullback of `β` along `b` across the outer rectangle is
pulling back along `e'` the transport of `β`, read through the composition isomorphisms. -/
theorem inverseImageSquareTransport_paste {S'' Y' : Scheme.{u}} (b : S'' ⟶ S') (h' : Y' ⟶ S'')
    (e' : Y' ⟶ Y) (Q : Y' ⟶ S') (hQh : Q = h' ≫ b) (hQe : Q = e' ≫ h)
    (a'' : S'' ⟶ S) (ha : a'' = b ≫ a) (e'' : Y' ⟶ X) (he : e'' = e' ≫ e) (P'' : Y' ⟶ S)
    (hP''h : P'' = h' ≫ a'') (hP''e : P'' = e'' ≫ g) {A K : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : (smallEtalePullbackAb a).obj A ⟶ (smallEtalePullbackAb a).obj K) :
    inverseImageSquareTransport a'' g h' e'' P'' hP''h hP''e
        (smallEtalePullbackAbConj b a a'' ha ((smallEtalePullbackAb b).map β)) =
      smallEtalePullbackAbConj e' e e'' he
        ((smallEtalePullbackAb e').map (inverseImageSquareTransport a g h e P hPh hPe β)) := by
  have hQa : P'' = Q ≫ a := by rw [hP''h, ha, hQh, Category.assoc]
  have heP : P'' = e' ≫ P := by rw [hP''e, he, hPe, Category.assoc]
  apply smallEtalePullbackAbConj_injective (f₁ := e'') (f₂ := g) (P := P'') (hP := hP''e)
  rw [smallEtalePullbackAbConj_inverseImageSquareTransport,
    smallEtalePullbackAbConj_assoc a b h' a'' ha Q hQh P'' hQa hP''h,
    smallEtalePullbackAbConj_map,
    ← smallEtalePullbackAbConj_assoc g e e' P hPe e'' he P'' hP''e heP,
    smallEtalePullbackAbConj_inverseImageSquareTransport,
    smallEtalePullbackAbConj_assoc a h e' P hPh Q hQe P'' hQa heP, smallEtalePullbackAbConj_map]

end Square

end Stacks.EtaleCohomology

end
